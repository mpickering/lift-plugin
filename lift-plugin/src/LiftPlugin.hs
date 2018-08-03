{-# LANGUAGE TupleSections #-}
module LiftPlugin
  ( plugin, p, Code(..), Ops, Identity(..), runCode )
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
import qualified Panic as GHC
import qualified ConLike as GHC
import HsDumpAst
import Data.Functor.Identity

import Control.Monad.IO.Class ( liftIO )

import Data.Generics ( everywhereM,  mkM )


import Language.Haskell.TH.Syntax (Lift(..), unsafeTExpCoerce, TExp, Q)

-- Library

class Ops r where
  p :: Lift a => a -> r a

newtype Code a = Code (Q (TExp a))

runCode (Code a) = a

instance Ops Code where
  p = Code . unsafeTExpCoerce . lift

instance Ops Identity where
  p = Identity

-- Plugin definitions

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const (Just liftPlugin)
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
  pprTrace "solveGCD" (ppr gs $$ ppr ds $$ ppr wanteds) $
  (return $! case failed of
    [] -> TcPluginOk (mapMaybe (\c -> (,c) <$> evMagic c) solved) []
    f  -> TcPluginContradiction f)
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

-- | TODO: Check here for (->) instance
evMagic :: Ct -> Maybe EvTerm
evMagic ct = case GHC.classifyPredType $ ctEvPred $ ctEvidence ct of
    GHC.ClassPred _tc _tys -> Just (EvExpr (Var fake_id))
    _                  -> Nothing

-- What this is doens't matter really
fake_id :: GHC.Id
fake_id = rUNTIME_ERROR_ID

-----------------------------------------------------------------------------
-- The source plugin which fills in the dictionaries magically.

replaceLiftDicts :: [GHC.CommandLineOption] -> GHC.ModSummary -> TcGblEnv -> TcM TcGblEnv
replaceLiftDicts _opts _sum tc_env = do
  hscEnv <- GHC.getTopEnv


  GHC.Found _ pluginModule <-
    liftIO
      ( GHC.findImportedModule
          hscEnv
          ( GHC.mkModuleName "LiftPlugin" )
          Nothing
      )

  -- This is the identifier we want to give some magic behaviour
  pName <-
    GHC.lookupId
      =<< GHC.lookupOrig pluginModule ( GHC.mkVarOcc "p" )

  -- We now look everywhere for it and replace the `Lift` dictionaries
  -- where we find it.
  new_tcg_binds <-
     mkM ( rewriteLiftDict pName ) `everywhereM` GHC.tcg_binds tc_env

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

con_pat_body :: GHC.Name -> Expr.LHsExpr GHC.GhcRn
con_pat_body v = GHC.noLoc (Expr.RecordCon GHC.noExt (GHC.noLoc v) flds)
  where
    flds = GHC.HsRecFields [] Nothing

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

