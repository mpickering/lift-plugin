{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
module LiftPlugin
  ( plugin, Pure(..), Syntax(..), overload )
where

-- external
import Data.Maybe          (mapMaybe)
import GHC.TcPluginM.Extra (lookupModule, lookupName)


-- GHC API
import FastString (fsLit)
import Module     (mkModuleName)
import OccName    (mkTcOcc)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence
import TcPluginM  (TcPluginM, tcLookupTyCon)
import TcRnTypes
import TyCon      (TyCon, tyConSingleDataCon)
import TyCoRep    (Type (..))
import Outputable
import Class
import MkCore
import CoreSyn
import Bag
import MonadUtils
import TcErrors
import Literal
import PrelNames
import HsDumpAst
import qualified Unique as GHC
import qualified THNames as GHC

import qualified IdiomsPlugin as Idioms

import Panic


-- ghc
import qualified Desugar as GHC
import qualified Finder as GHC
import qualified GHC hiding (exprType)
import qualified GhcPlugins as GHC
import qualified HsExpr as Expr
import qualified IfaceEnv as GHC
import qualified TcEvidence as GHC
import qualified TcRnMonad as GHC
import qualified TysPrim as GHC

import Control.Monad.IO.Class ( liftIO )
import Control.Monad

import Data.Generics ( everywhereM,  mkM, listify, everywhere, mkT
                     , everywhereBut, mkQ )
import Data.List

import GHC.Generics

import Data.Function


import Language.Haskell.TH.Syntax (Lift(..))

import Data.IORef
import System.IO.Unsafe

-- In this IORef we store how we would have reported the error
ioRef :: IORef (Int, [TcM ()])
ioRef = unsafePerformIO (newIORef (0, []))
{-# NOINLINE ioRef #-}

addError :: TcM () -> IO Int
addError err = atomicModifyIORef ioRef (\(k, errs) -> ((k+1, errs ++ [err]), k))

getError :: Int -> IO (TcM ())
getError k = (!! k) . snd <$> readIORef ioRef

-- Library

class Pure r where
  pure :: Lift a => a -> r a

-- Syntax we can overload
class (Pure r) => Syntax r where
  -- Simple overloading
  _if :: r Bool -> r a -> r a -> r a
  _lam :: (r a -> r b) -> r (a -> b)
  _let :: r a -> (r a -> r b) -> r b
  _ap :: r (a -> b) -> r a -> r b


  -- Case overloading
  _uncons ::  r [a] -> r res -> (r a -> r [a] -> r res) -> r res
  _elim_prod :: r (a, b) -> (r a -> r b -> r x) -> r x



overload :: Syntax r => a -> r a
overload = undefined
{-# NOINLINE overload #-}

data Names a = Names
  { pureName, ifName, unconsName, lamName, letName, elimProdName, apName
    , overloadName :: a }
  deriving (Functor, Traversable, Foldable, Generic)

namesString :: Names String
namesString =
  Names
    { pureName = "pure"
    , ifName = "_if"
    , unconsName = "_uncons"
    , lamName = "_lam"
    , letName = "_let"
    , elimProdName = "_elim_prod"
    , apName = "_ap"
    , overloadName = "overload"
    }


-- Maps a representative name to the ordering and constructors we expect
-- with their arity
caseTable :: GHC.NameEnv CaseRow
caseTable = GHC.mkNameEnv [(fst (head (caseInfo ci)), ci) | ci <- caseTableInfo ]

data CaseRow = CaseRow { _overloadCase :: (forall a . Names a -> a)
                       , caseInfo :: [(GHC.Name, Int)]
                       }

-- mkCaseRow enforces the ordering invariant
mkCaseRow :: (forall a . Names a -> a) -> [(GHC.Name, Int)] -> CaseRow
mkCaseRow sel info = CaseRow sel (sortBy (GHC.stableNameCmp `on` fst) info)

tuple2Name :: GHC.Name
tuple2Name = GHC.dataConName (GHC.tupleDataCon GHC.Boxed 2)

caseTableInfo :: [CaseRow]
caseTableInfo =
  [ mkCaseRow unconsName [(GHC.consDataConName, 2), (GHC.nilDataConName, 0)]
  , mkCaseRow elimProdName [(tuple2Name, 2)] ]





-- Plugin definitions

plugin :: Plugin
plugin = defaultPlugin { parsedResultAction = parsedResultAction (Idioms.plugin)
                       , renamedResultAction = overloadedSyntax
                       , tcPlugin = const (Just liftPlugin)
                       , typeCheckResultAction = replaceLiftDicts }

liftPlugin :: TcPlugin
liftPlugin =
  TcPlugin { tcPluginInit  = lookupLiftTyCon
           , tcPluginSolve = solveLift
           , tcPluginStop  = const (return ())
           }


lookupLiftTyCon :: TcPluginM TyCon
lookupLiftTyCon = do
    md      <- lookupModule liftModule liftPackage
    liftTcNm <- lookupName md (mkTcOcc "Lift")
    tcLookupTyCon liftTcNm
  where
    liftModule  = mkModuleName "Language.Haskell.TH.Syntax"
    liftPackage = fsLit "template-haskell"


-- This plugin solves all instances of (Lift (a -> b)) with a dummy value.
solveLift :: TyCon -- ^ Lift's TyCon
         -> [Ct]  -- ^ [G]iven constraints
         -> [Ct]  -- ^ [D]erived constraints
         -> [Ct]  -- ^ [W]anted constraints
         -> TcPluginM TcPluginResult
solveLift _     _ _ []      = return (TcPluginOk [] [])
solveLift liftTc gs ds wanteds =
  pprTrace "solveGCD" (ppr gs $$ ppr ds $$ ppr wanteds) $ do
    res <- mapM (\c -> (, c) <$> evMagic c) solved
    return $! case failed of
      [] -> TcPluginOk res []
      f  -> TcPluginContradiction f
  where
    liftWanteds :: [Ct]
    liftWanteds = mapMaybe (toLiftCt liftTc) wanteds

    solved, failed :: [Ct]
    (solved,failed) = (liftWanteds, [])

toLiftCt :: TyCon -> Ct -> Maybe Ct
toLiftCt liftTc ct =
  case GHC.classifyPredType $ ctEvPred $ ctEvidence ct of
    GHC.ClassPred tc tys
     | pprTrace "classPred" (ppr (classTyCon tc) $$ ppr liftTc $$ ppr (classTyCon tc == liftTc)) True
     , classTyCon tc == liftTc
     , [ty] <- tys
     , GHC.isFunTy ty
      -> Just ct
    _ -> Nothing

mkWC :: Ct -> WantedConstraints
mkWC ct = WC (unitBag ct) emptyBag

addErrTc :: TcM () -> TcPluginM Int
addErrTc err = unsafeTcPluginTcM (liftIO (addError err))
getErrTc :: Int -> TcM ()
getErrTc k = join (liftIO (getError k))


-- | TODO: Check here for (->) instance
evMagic :: Ct -> TcPluginM EvTerm
evMagic ct = do
  let reporter = reportAllUnsolved (mkWC ct)
  k <- addErrTc reporter
  return $ (EvExpr (FakeExpr (ctPred ct) k))

-- What this is doens't matter really
fakeIdName :: GHC.Name
fakeIdName = GHC.mkWiredInIdName gHC_MAGIC (fsLit "fake_id") fakeIdKey fakeId

fakeIdKey :: Unique
fakeIdKey = GHC.mkPreludeMiscIdUnique 109

fakeId :: GHC.Id
fakeId = GHC.mkVanillaGlobalWithInfo fakeIdName ty info
  where
    info = GHC.noCafIdInfo
    ty = GHC.mkSpecForAllTys [GHC.alphaTyVar] (GHC.mkFunTy GHC.intTy GHC.alphaTy)

fake_id = fakeId

is_fake_id :: GHC.Id -> Bool
is_fake_id = (== fake_id)

fake_expr :: Type -> Int -> Expr GHC.Id
fake_expr ty k = mkCoreApps (Var fake_id) [Type ty, (Lit $ LitNumber LitNumInteger (fromIntegral k) GHC.intTy)]

pattern FakeExpr :: Type -> Int -> Expr GHC.Id
pattern FakeExpr ty k <- App (App (Var (is_fake_id -> True)) (Type ty)) (Lit (LitNumber LitNumInteger (fromIntegral -> k) _))
  where
    FakeExpr k = fake_expr k

-----------------------------------------------------------------------------
-- The source plugin which fills in the dictionaries magically.

lookupIds :: GHC.Module -> Names String -> TcM (Names GHC.Id)
lookupIds pm = traverse (\s -> GHC.lookupId =<< GHC.lookupOrig pm (GHC.mkVarOcc s))

lookupNames :: GHC.Module -> Names String -> TcM (Names GHC.Name)
lookupNames pm = traverse (\s -> GHC.lookupOrig pm (GHC.mkVarOcc s))

replaceLiftDicts :: [GHC.CommandLineOption] -> GHC.ModSummary -> TcGblEnv -> TcM TcGblEnv
replaceLiftDicts _opts _sum tc_env = do
  hscEnv <- GHC.getTopEnv
  v <- liftIO (readIORef ioRef)
  pprTrace "ioRef" (ppr (length v)) (return ())
  --getErrTc 0

  GHC.Found _ pluginModule <-
    liftIO
      ( GHC.findImportedModule
          hscEnv
          ( GHC.mkModuleName "LiftPlugin" )
          Nothing
      )

  -- This is the identifier we want to give some magic behaviour
  Names{..} <- lookupIds pluginModule namesString

  -- We now look everywhere for it and replace the `Lift` dictionaries
  -- where we find it.
  new_tcg_binds <-
     mkM ( rewriteLiftDict pureName ) `everywhereM` GHC.tcg_binds tc_env

  -- Check if there are any instances which remain unsolved
  checkUsages (GHC.tcg_ev_binds tc_env) new_tcg_binds

  return tc_env { GHC.tcg_binds = new_tcg_binds }

-- |
rewriteLiftDict :: GHC.Id -> Expr.LHsExpr GHC.GhcTc -> GHC.TcM ( Expr.LHsExpr GHC.GhcTc )
rewriteLiftDict pName
  e@( GHC.L _ ( Expr.HsApp _ ( GHC.L _ ( Expr.HsWrap _ _ ( Expr.HsVar _ ( GHC.L _ v ) ) ) ) body) )
    | pName == v
    = mkM (repair body) `everywhereM` e
rewriteLiftDict _ e =
 -- pprTrace "rewriteAssert" (ppr e $$ showAstData NoBlankSrcSpan e) $
   return e


checkLiftable_var :: Expr.LHsExpr GHC.GhcRn -> GHC.Id -> TcM (Maybe GHC.CoreExpr)
-- Externally defined names
checkLiftable_var body var
 | GHC.isGlobalId var = Just <$> mkSplice body
-- Top-level names
checkLiftable_var body var = do
  env <- tcg_type_env <$> GHC.getGblEnv
  case GHC.lookupNameEnv env (GHC.idName var) of
    Just _ -> Just <$> mkSplice body
    Nothing -> return Nothing

checkLiftable :: Expr.LHsExpr GHC.GhcTc -> GHC.TcM (Maybe GHC.EvExpr)
checkLiftable e | Just e' <- wrapView e = checkLiftable e'
checkLiftable (GHC.L _ (Expr.HsVar _ v)) = checkLiftable_var (var_body $ GHC.getName v) (GHC.unLoc v)
checkLiftable (GHC.L _ (Expr.HsConLikeOut _ c)) = do
  Just <$> mkSplice (var_body $ GHC.getName c)
checkLiftable _ = return Nothing

wrapView :: Expr.LHsExpr GHC.GhcTc -> Maybe (GHC.LHsExpr GHC.GhcTc)
wrapView (GHC.L l (Expr.HsWrap _ _ e)) = Just (GHC.L l e)
wrapView _ = Nothing


-- We take the body and then look for all the `Lift` dictionaries to
-- replace them by a special one which ignores the argument.
-- The only case we deal with currently is if the `body` is a simple
-- variable. This won't deal with polymorphic functions yet.
repair :: Expr.LHsExpr GHC.GhcTc -> GHC.EvExpr -> GHC.TcM (GHC.EvExpr)
repair expr e = do
  let e_ty = GHC.exprType e
      (ty_con, tys) = GHC.splitTyConApp e_ty
      res = ty_con `GHC.hasKey` GHC.liftClassKey
  pprTrace "repair" (ppr ty_con $$ ppr tys $$ ppr res) $
    if (ty_con `GHC.hasKey` GHC.liftClassKey)
        && GHC.isFunTy (head tys)
      then do
        mres <- checkLiftable expr
        case mres of
          Just evidence -> return $ mkLiftDictionary (tyConSingleDataCon ty_con) e_ty evidence
          Nothing -> do
            makeError expr
            -- Return e to keep going
            return e
            --GHC.panicDoc "skipping" (ppr expr $$ showAstData BlankSrcSpan expr)
      else
        pprTrace "skipping1" (ppr expr) $
        return e

makeError :: Expr.LHsExpr GHC.GhcTc -> GHC.TcM ()
makeError (GHC.L l e) =
  GHC.setSrcSpan l $
  GHC.addErrCtxt (text "In" <+> ppr e) $
  GHC.failWithTc msg
  where
    msg = text "Unable to magically lift the argument."
          <+> text "It probably isn't statically known."




{-
  mb_local_use <- GHC.getStageAndBindLevel (GHC.idName v)
  case mb_local_use of
    Just (top_level, bind_lvl, use_stage)
      | GHC.isNotTopLevel top_level
      -> GHC.panicDoc "error" (ppr v)
    _ -> return .
repair e = return e
-}

var_body :: GHC.Name -> Expr.LHsExpr GHC.GhcRn
var_body v = (GHC.noLoc (Expr.HsVar GHC.noExt (GHC.noLoc v)))

mkSplice :: Expr.LHsExpr GHC.GhcRn -> TcM CoreExpr
mkSplice body = do
  hs_env  <- GHC.getTopEnv
  -- [|| var ||]
  let e = GHC.noLoc $ Expr.HsTcBracketOut GHC.noExt (Expr.TExpBr GHC.noExt body) []

  ( _, mbe ) <- liftIO ( GHC.deSugarExpr hs_env e )

  case mbe of
    Nothing -> panic "failed" -- Not sure what situation this happens.
    Just core_e -> return core_e

-- | Construct the specialised dictionary which constructs `[|| foo ||]`
-- from `lift foo`
mkLiftDictionary :: GHC.DataCon -> Type -> CoreExpr -> CoreExpr
mkLiftDictionary dc ty splice =
  let lvar = GHC.mkTemplateLocal 0 ty
  in mkCoreConApps dc [Type ty, mkCoreLams [lvar] splice]

---- Checking Usages
-- TODO: I think we could store the landmine usage from the Ct information
-- in the type checking plugin
checkUsages :: Bag EvBind -> GHC.LHsBinds GHC.GhcTc -> TcM ()
checkUsages (bagToList -> bs) binds = do
  let landmines = getFakeDicts bs
      -- TODO: Use synthesise here?
      go :: TcEvBinds -> Bool
      go (EvBinds _) = True
      go _ = False
      extract = concatMap (\(EvBinds b) -> getFakeDicts (bagToList b))
      landmines' = extract $ listify go binds
      -- Get all variable usages, we don't want any landmines to appear.
      all_vars :: EvExpr -> Bool
      all_vars (Var _) = True
      all_vars _ = False
      usages = map (\(Var v) -> v) (listify all_vars binds)
  pprTrace "landmines" (ppr landmines) (return ())
  pprTrace "landmines'" (ppr landmines') (return ())
  pprTrace "usages" (ppr usages) (return ())
  pprTrace "dicts" (ppr bs) (return ())
  mapM_ (checkMine usages) (landmines ++ landmines')

-- Check whether a mine appears in the program.
checkMine :: [GHC.EvVar] -> (GHC.EvVar, Int) -> TcM ()
checkMine uses (v, k) = when (v `elem` uses) (getErrTc k)

getFakeDicts :: [EvBind] -> [(GHC.EvVar, Int)]
getFakeDicts = mapMaybe getFakeDict
  where
    getFakeDict (EvBind r (EvExpr (FakeExpr _ k)) _) = Just (r, k)
    getFakeDict _ = Nothing


{-----------------------------------------------------------------------------
-  The parser plugin - implement our own overloaded syntax
-  --------------------------------------------------------------------------}

overloadedSyntax
  :: [GHC.CommandLineOption] -> TcGblEnv -> GHC.HsGroup GHC.GhcRn
                                         -> TcM (TcGblEnv, GHC.HsGroup GHC.GhcRn)
overloadedSyntax _opts tc_gbl_env rn_group = do
  hscEnv <- GHC.getTopEnv
  GHC.Found _ pluginModule <-
    liftIO
      ( GHC.findImportedModule
          hscEnv
          ( GHC.mkModuleName "LiftPlugin" )
          Nothing
      )
  namesName <- lookupNames pluginModule namesString

  let new_group = everywhere (mkT (overload_guard namesName)) rn_group
  return (tc_gbl_env, new_group)

pattern VarApp :: GHC.Name -> Expr.LHsExpr GHC.GhcRn -> Expr.LHsExpr GHC.GhcRn
pattern VarApp v e <- (GHC.unLoc -> Expr.HsApp _ (GHC.unLoc -> Expr.HsVar _ (GHC.unLoc -> v)) e)

is_dollar :: GHC.Name -> Bool
is_dollar = (== dollarName)

pattern DollarVarApp :: GHC.Name -> Expr.LHsExpr GHC.GhcRn -> Expr.LHsExpr GHC.GhcRn
pattern DollarVarApp v e <- (GHC.unLoc -> Expr.OpApp _ (GHC.unLoc -> Expr.HsVar _ (GHC.unLoc -> v)) (GHC.unLoc -> Expr.HsVar _ (is_dollar . GHC.unLoc -> True)) e)

-- Look for direct applications of `overload e` or `overload $ e` and then
-- perform the overloading.
overload_guard :: Names GHC.Name -> Expr.LHsExpr GHC.GhcRn
                                                 -> Expr.LHsExpr GHC.GhcRn
overload_guard names old_e =
  case old_e of
    VarApp v e -> check_overload_app names v e old_e
    DollarVarApp v e -> check_overload_app names v e old_e
    _ -> old_e


check_overload_app :: Names GHC.Name -> GHC.Name -> Expr.LHsExpr GHC.GhcRn
                                                 -> Expr.LHsExpr GHC.GhcRn
                                                 -> Expr.LHsExpr GHC.GhcRn
check_overload_app names@(Names { overloadName } ) v e old_e
  | v == overloadName = overload_scope names e
  | otherwise = old_e

-- Now perform the overriding just on the expression in this scope.
overload_scope :: Names GHC.Name -> Expr.LHsExpr GHC.GhcRn
                                                 -> Expr.LHsExpr GHC.GhcRn
overload_scope names e =
    let mkVar = GHC.noLoc . Expr.HsVar GHC.noExt . GHC.noLoc
        namesExpr = fmap (\n -> ExprWithName n (mkVar n)) names
    in everywhereBut (mkQ False (check_pure namesExpr)) (mkT (overloadExpr namesExpr)) e

data ExprWithName = ExprWithName { ename :: GHC.Name, mkExpr :: (Expr.LHsExpr GHC.GhcRn) }

-- Don't recurse into pure
check_pure :: Names ExprWithName -> Expr.LHsExpr GHC.GhcRn -> Bool
check_pure Names{..} (GHC.L _ e) = go e
  where
    go (Expr.HsApp _exp (GHC.L _ (Expr.HsVar _ name)) _)
      | GHC.unLoc name == ename pureName = True
    go _ = False

overloadExpr :: Names ExprWithName -> Expr.LHsExpr GHC.GhcRn -> Expr.LHsExpr GHC.GhcRn
overloadExpr names@Names{..} le@(GHC.L l e) = go e
  where
    go (Expr.HsIf _ext _ p te fe) =
      pprTrace "Replacing if" (ppr e)
       $ foldl' GHC.mkHsApp (mkExpr ifName) [p, te, fe]
    go (Expr.HsApp _exp e1 e2) =
      pprTrace "Replacing app" (ppr e)
       $ foldl' GHC.mkHsApp (mkExpr apName) [e1, e2]
    go (Expr.HsLam {}) =
      pprTrace "Replacing lam" (ppr e)
       $ GHC.mkHsApp (mkExpr lamName) le
    go (Expr.HsLet _ binds let_rhs) =
      let (binder, rhs) = extractBindInfo names binds
          pats = [GHC.noLoc $ GHC.VarPat GHC.noExt binder]
          body_lam = mkHsLam pats let_rhs
      in
        pprTrace "Replacing let" (ppr e $$ ppr rhs $$ ppr body_lam )
          $ foldl' GHC.mkHsApp (mkExpr letName) [rhs, body_lam]

    go (Expr.HsCase _ext scrut mg) =
      let res = caseDataCon names scrut mg
      in case res of
           Left err -> panic err
           Right expr -> expr

    go expr = GHC.L l expr

mkHsLam :: [GHC.LPat GHC.GhcRn] -> Expr.LHsExpr GHC.GhcRn -> Expr.LHsExpr (GHC.GhcRn)
mkHsLam pats body = mkHsLamGRHS pats (GHC.unguardedGRHSs body)

mkHsLamGRHS :: [GHC.LPat GHC.GhcRn] -> Expr.GRHSs GHC.GhcRn (GHC.LHsExpr GHC.GhcRn)
                                    -> Expr.LHsExpr (GHC.GhcRn)
mkHsLamGRHS [] (Expr.GRHSs { grhssGRHSs = grhss, grhssLocalBinds = (GHC.L _ (GHC.EmptyLocalBinds _)) }) =
  case grhss of
    [GHC.L _ grhs] -> case simpleGRHS grhs of
                Just e -> e
                Nothing -> panic "GRHS is not simple2"

    _ -> panic "GRHS is not simple"
mkHsLamGRHS pats grhs = body_lam
  where
    matches = GHC.mkMatchGroup GHC.Generated [mkGRHSMatch pats grhs]
    body_lam = GHC.noLoc $ GHC.HsLam GHC.noExt matches

mkGRHSMatch :: (GHC.XCMatch p body ~ GHC.NoExt) =>
                     [GHC.LPat p]
                     -> Expr.GRHSs p body -> GHC.Located (Expr.Match p body)
mkGRHSMatch pats rhs = GHC.noLoc $ GHC.Match GHC.noExt GHC.LambdaExpr pats rhs

{- Code for dealing with let -}

-- Get the binder and body of let
extractBindInfo :: Names ExprWithName -> GHC.LHsLocalBinds GHC.GhcRn -> (GHC.Located GHC.Name, GHC.LHsExpr GHC.GhcRn)
extractBindInfo names (GHC.L _ (GHC.HsValBinds _ (GHC.XValBindsLR (GHC.NValBinds binds _)))) = getBinds binds
  where
    getBinds bs =
      let [rs] = map snd bs
      in
      case bagToList rs of
        [GHC.L _ (GHC.FunBind _ bid matches _ _)] ->
          case isSimpleMatchGroup matches of
            Just simple -> (bid, simple)
            _ -> (bid, overloadExpr names (GHC.noLoc $ Expr.HsLam GHC.noExt matches))
        -- Not dealing with guards here yet but they could be
        -- transfered onto the lambda
        _ -> panic "abc"
extractBindInfo _ e = panicDoc "abc2" (showAstData BlankSrcSpan e)

simpleGRHS :: Expr.GRHS p w -> Maybe w
simpleGRHS grhs =
  case grhs of
    (Expr.GRHS _ [] body) -> Just body
    _ -> Nothing

-- A simple match group is one which is just a variable with no
-- arguments.
-- let x = y
isSimpleMatchGroup :: Expr.MatchGroup id body -> Maybe body
isSimpleMatchGroup (Expr.MG { mg_alts = matches })
  | [GHC.L _ match] <- GHC.unLoc matches
  , Expr.Match { m_grhss = GHC.GRHSs { grhssGRHSs = [rhs] }
               , m_pats = [] } <- match
  = simpleGRHS (GHC.unLoc rhs)
  | otherwise
  = Nothing
isSimpleMatchGroup (Expr.XMatchGroup _) = panic "unhandled"

{- Code for dealing with case -}

--sd :: Data a => a -> SDoc
--sd = showAstData BlankSrcSpan

--deriving instance Data p => Data (Expr.Match p (Expr.LHsExpr p))

-- Look at a case and see if it's a simple match on a data con
caseDataCon :: Names ExprWithName
            -> Expr.LHsExpr (GHC.GhcRn)
            -> Expr.MatchGroup (GHC.GhcRn) (Expr.LHsExpr (GHC.GhcRn))
            -> Either String (GHC.LHsExpr GHC.GhcRn)
caseDataCon names scrut (Expr.MG { mg_alts = (GHC.L _l alts) }) = do
  res <- sortBy (\(_, n, _) (_, n1, _)-> GHC.stableNameCmp n n1) <$>
              (mapM (extractConDetails . GHC.unLoc) $ alts)
  case res of
    [] -> Left "No patterns"
    ps@((_, n, _):_) ->
      case GHC.lookupNameEnv caseTable n of
        Nothing -> Left "Not able to overload this constructor"
        Just (CaseRow sel spec) ->
          let con = GHC.mkHsApp (mkExpr (sel names)) scrut
          in checkAndBuild con ps spec
caseDataCon _ _ (Expr.XMatchGroup _) = panic "unhandled"

checkAndBuild :: Expr.LHsExpr GHC.GhcRn -- The constructor
              -> [([GHC.LPat GHC.GhcRn], GHC.Name
                                       , Expr.GRHSs GHC.GhcRn (GHC.LHsExpr GHC.GhcRn))]
              -> [(GHC.Name, Int)]
              -> Either String (Expr.LHsExpr GHC.GhcRn)
checkAndBuild con [] [] = Right con
checkAndBuild _con (_:_) [] = Left "Too many patterns in program"
checkAndBuild _con [] (_:_) = Left "Not enough patterns in program"
checkAndBuild con (p:ps) (s:ss) = do
  res <- checkAndBuild con ps ss
  let (pats, pat_con, rhs) = p
      (spec_con, arity) = s
  if | pat_con /= spec_con -> Left "Constructors do not match"
     | length pats /= arity -> Left "Arity does not patch"
     | otherwise -> Right (GHC.mkHsApp res (mkHsLamGRHS pats rhs))








-- Extract, binders, con name and rhs
extractConDetails :: Expr.Match GHC.GhcRn body
                  -> Either String ([GHC.LPat GHC.GhcRn], GHC.Name, Expr.GRHSs GHC.GhcRn body)
-- There should only be one pattern in a case
extractConDetails (Expr.Match { m_pats = [pat], m_grhss = rhs }) = do
  (vars, cn) <- extractFromPat pat
  return (vars, cn, rhs)
extractConDetails _ = Left "More than one match"

extractFromPat :: GHC.LPat GHC.GhcRn -> Either String ([GHC.LPat GHC.GhcRn], GHC.Name)
extractFromPat (GHC.L _l p) =
  case p of
    GHC.ConPatIn (GHC.L _l n) con_pat_details
      -> Right (GHC.hsConPatArgs con_pat_details, n)
    GHC.ParPat _ pp -> extractFromPat pp
    GHC.TuplePat _ [a, b] GHC.Boxed ->
      Right ([a, b], tuple2Name)
    _ -> Left "Complex pattern"

