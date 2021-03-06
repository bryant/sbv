-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.CVC4
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the CVC4 SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.CVC4(cvc4) where

import qualified Control.Exception as C

import Data.Char          (isSpace)
import Data.Function      (on)
import Data.List          (sortBy, intercalate)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (mkSkolemZero)
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.Utils.Lib (splitArgs)

-- | The description of the CVC4 SMT solver
-- The default executable is @\"cvc4\"@, which must be in your path. You can use the @SBV_CVC4@ environment variable to point to the executable on your system.
-- The default options are @\"--lang smt\"@. You can use the @SBV_CVC4_OPTIONS@ environment variable to override the options.
cvc4 :: SMTSolver
cvc4 = SMTSolver {
           name           = CVC4
         , executable     = "cvc4"
         , options        = ["--lang", "smt"]
         , engine         = \cfg isSat qinps modelMap skolemMap pgm -> do
                                    execName <-                   getEnv "SBV_CVC4"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (splitArgs `fmap` getEnv "SBV_CVC4_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts} }
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Just (cont (roundingMode cfg) skolemMap)}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap isSat qinps modelMap))
         , xformExitCode  = id
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "CVC4"
                                , mbDefaultLogic             = Just "ALL_SUPPORTED"  -- CVC4 is not happy if we don't set the logic, so fall-back to this if necessary
                                , supportsMacros             = True
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = True
                                , supportsUninterpretedSorts = True
                                , supportsUnboundedInts      = True
                                , supportsReals              = True  -- Not quite the same capability as Z3; but works more or less..
                                , supportsFloats             = False
                                , supportsDoubles            = False
                                }
         }
 where cont rm skolemMap = intercalate "\n" $ map extract skolemMap
        where extract (Left s)        = "(echo \"((" ++ show s ++ " " ++ mkSkolemZero rm (kindOf s) ++ "))\")"
              extract (Right (s, [])) = "(get-value (" ++ show s ++ "))"
              extract (Right (s, ss)) = "(get-value (" ++ show s ++ concat [' ' : mkSkolemZero rm (kindOf a) | a <- ss] ++ "))"
       addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "CVC4: Timeout value must be non-negative, received: " ++ show i
         | True                = o ++ ["--tlimit=" ++ show i ++ "000"]  -- SBV takes seconds, CVC4 wants milli-seconds

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap isSat qinps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine inps . unstring) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        inps -- for "sat", display the prefix existentials. For completeness, we will drop
             -- only the trailing foralls. Exception: Don't drop anything if it's all a sequence of foralls
             | isSat = map snd $ if all (== ALL) (map fst qinps)
                                 then qinps
                                 else reverse $ dropWhile ((== ALL) . fst) $ reverse qinps
             -- for "proof", just display the prefix universals
             | True  = map snd $ takeWhile ((== ALL) . fst) qinps
        -- CVC4 puts quotes around echo's, go figure. strip them here
        unstring s' = case (s, head s, last s) of
                        (_:tl@(_:_), '"', '"') -> init tl
                        _                      -> s'
          where s = reverse . dropWhile isSpace . reverse . dropWhile isSpace $ s'
