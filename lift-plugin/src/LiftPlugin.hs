{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module LiftPlugin
  ( plugin, Pure(..), Syntax(..) )
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
import qualified Unique as GHC
import qualified THNames as GHC


-- ghc
import qualified Desugar as GHC
import qualified Finder as GHC
import qualified GHC hiding (exprType)
import qualified GhcPlugins as GHC
import qualified HsExpr as Expr
import qualified IfaceEnv as GHC
import qualified TcEvidence as GHC
import qualified TcRnMonad as GHC

import Control.Monad.IO.Class ( liftIO )
import Control.Monad

import Data.Generics ( everywhereM,  mkM, listify, everywhere, mkT )
import Data.List

import GHC.Generics


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
  _if :: r Bool -> r a -> r a -> r a
  _uncons ::  r [a] -> (r a -> r [a] -> r res) -> r res -> r res
  _lam :: (r a -> r b) -> r (a -> b)
  _let :: r a -> (r a -> r b) -> r b
  _elim_prod :: r (a, b) -> (r a -> r b -> r x) -> r x
  _ap :: r (a -> b) -> r a -> r b

data Names a = Names
  { pureName, ifName, unconsName, lamName, letName, elimProdName, apName :: a }
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
    }


-- Plugin definitions

plugin :: Plugin
plugin = defaultPlugin { parsedResultAction = overloadedSyntax
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
    res <- mapMaybeM (\c -> fmap (, c) <$> evMagic c) solved
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
evMagic :: Ct -> TcPluginM (Maybe EvTerm)
evMagic ct = case GHC.classifyPredType $ ctEvPred $ ctEvidence ct of
    GHC.ClassPred _tc _tys -> do
      let reporter = reportAllUnsolved (mkWC ct)
      k <- addErrTc reporter
      return $ Just (EvExpr (FakeExpr k))
    _                  -> return Nothing

-- What this is doens't matter really
fake_id :: GHC.Id
fake_id = rUNTIME_ERROR_ID

is_fake_id :: GHC.Id -> Bool
is_fake_id = (== fake_id)

fake_expr :: Int -> Expr GHC.Id
fake_expr k = App (Var fake_id) (Lit $ LitNumber LitNumInteger (fromIntegral k) GHC.intTy)

pattern FakeExpr :: Int -> Expr GHC.Id
pattern FakeExpr k <- App (Var (is_fake_id -> True)) (Lit (LitNumber LitNumInteger (fromIntegral -> k) _))
  where
    FakeExpr k = fake_expr k

-----------------------------------------------------------------------------
-- The source plugin which fills in the dictionaries magically.

lookupNames :: GHC.Module -> Names String -> TcM (Names GHC.Id)
lookupNames pm = traverse (\s -> GHC.lookupId =<< GHC.lookupOrig pm (GHC.mkVarOcc s))

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
  Names{..} <- lookupNames pluginModule namesString

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
    getFakeDict (EvBind r (EvExpr (FakeExpr k)) _) = Just (r, k)
    getFakeDict _ = Nothing


{-----------------------------------------------------------------------------
-  The parser plugin - implement our own overloaded syntax
-  --------------------------------------------------------------------------}

overloadedSyntax
  :: [GHC.CommandLineOption] -> GHC.ModSummary -> GHC.HsParsedModule
                                               -> GHC.Hsc GHC.HsParsedModule
overloadedSyntax _opts _ms parsed_mod
  =
  let mkVar = GHC.noLoc . Expr.HsVar GHC.noExt . GHC.noLoc
            . GHC.mkRdrUnqual . GHC.mkVarOcc
      namesRDR = fmap mkVar namesString
      new_mod = (everywhere (mkT (overload namesRDR)) (GHC.hpm_module parsed_mod))
  in return (parsed_mod { GHC.hpm_module = new_mod })

overload :: Names (Expr.LHsExpr GHC.GhcPs) -> Expr.LHsExpr GHC.GhcPs -> Expr.LHsExpr GHC.GhcPs
overload Names{..} (GHC.L l e) = go e
  where
    go (Expr.HsIf _ext _ p te fe) =
      pprTrace "Replacing if" (ppr e)
       $ foldl' GHC.mkHsApp ifName [p, te, fe]
    go expr = GHC.L l expr


