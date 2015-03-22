module Data.SBV.Provers.STP where

import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (mkSkolemZero)
import Data.SBV.Utils.Lib (splitArgs)
import Data.List          (sortBy, intercalate)
import Data.Char          (isSpace)
import Data.Function      (on)
import Control.Exception (catchJust, throw)
import Control.Monad (guard)
import System.Environment (getEnv)
import System.IO.Error (isDoesNotExistError)

stp :: SMTSolver
stp = SMTSolver
    { name = STP
    , executable = "stp"
    , options = ["--SMTLIB2"]
    , engine = stp_interp
    , xformExitCode = id
    , capabilities = stp_cap
    }

stp_cap = SolverCapabilities
        { capSolverName = "STP"
        , mbDefaultLogic = Nothing
        , supportsMacros = True
        , supportsProduceModels = False
        , supportsQuantifiers = True
        , supportsUninterpretedSorts = True
        , supportsUnboundedInts      = True
        , supportsReals              = True
        , supportsFloats             = True
        , supportsDoubles            = True
        }

--stp_interp :: SMTEngine
--SMTConfig -> Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [Either SW (SW, [SW])] -> String -> IO SMTResult

stp_interp cfg issat qinps modelmap skolem pgm = do
    exe <- fmap (maybe (executable solv) id) (mb_env "SBV_STP")
    opts <- fmap (maybe (options solv) splitArgs) (mb_env "SBV_STP_OPTIONS")
    let cfg_ = cfg { solver = solv { executable = exe, options = opts } }
    let script = SMTScript pgm Nothing -- $ (Just $ cont (roundingMode cfg) skolem)
    standardSolver cfg_ script id (ProofError cfg_)
                (interpretSolverOutput cfg_ $ extractMap issat qinps modelmap)
    where solv = solver cfg

mb_env envvar = catchJust (guard . isDoesNotExistError) (fmap Just $ getEnv envvar) $
        const (return Nothing)

cont rm skolemMap = intercalate "\n" $ map extract skolemMap
    where
    extract (Left s)        = "(echo \"((" ++ show s ++ " " ++ mkSkolemZero rm (kindOf s) ++ "))\")"
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
