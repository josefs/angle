module Language.Angle where

import Prelude hiding (seq)
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.List (sort)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

data Angle
  = Unit
  | Num Int
  | Pair Angle Angle
  | Inl Angle
  | Inr Angle
  | Arr [Angle]
  | Underscore
  | Choice Angle Angle
  | Var String
  | Pred String Angle
  | Seq Angle Angle
  | Eq Angle Angle
  | All Angle
  | Elements Angle
  | Never
  deriving (Show, Eq, Ord)

data Value
  = VUnit
  | VNum Int
  | VPair Value Value
  | VInl Value
  | VInr Value
  | VArr [Value]
  | VSet (Set Value)
  | VVar Int -- Unification variable
  deriving (Show, Eq, Ord)

type Env = Map String Value

-- Invariant: The values in the database are fully zonked (i.e., contain no variables)
type EDB = Map String [Value]

type IDB = Map String Angle

data DBs = DBs
  { edb :: EDB
  , idb :: IDB
  }

type Preds = Map String Angle

type Unif = (IntMap Value, Int)

-- The evaluation monad

type AngleM a = ReaderT DBs (StateT Env (StateT Unif (LogicT IO))) a

-- EDB takes precedence over IDB. We use that fact in fixpoint computations
lookupPred :: String -> AngleM (Either Angle [Value])
lookupPred name = do
  dbe <- asks edb
  case Map.lookup name dbe of
    Just vs -> return (Right vs)
    Nothing -> do
      dbi <- asks idb
      case Map.lookup name dbi of
        Just angle -> return (Left angle)
        Nothing -> mzero

localPred :: String -> [Value] -> AngleM a -> AngleM a
localPred name values =
  local (\dbs -> dbs { edb = Map.insert name values (edb dbs) })

lookupVar :: String -> AngleM (Maybe Value)
lookupVar x = do
  env <- lift get
  return $ Map.lookup x env

setVar :: String -> Value -> AngleM Value
setVar x v = do
  env <- lift get
  lift $ put (Map.insert x v env)
  return v

freshUnifVar :: AngleM Value
freshUnifVar = do
  (unifMap,n) <- lift $ lift get
  lift $ lift $ put (unifMap, n+1)
  return (VVar n)

lookupUnif :: Int -> AngleM (Maybe Value)
lookupUnif x = do
  (unif,_) <- lift $ lift get
  return $ IntMap.lookup x unif

setUnifVar :: Int -> Value -> AngleM Value
setUnifVar x v = do
  (unifMap,n) <- lift $ lift get
  lift $ lift $ put (IntMap.insert x v unifMap,n)
  return v

collectResults :: AngleM Value -> AngleM (Set Value)
collectResults m = do
  let rec accum angle = do
        res <- msplit angle
        case res of
          Nothing -> return accum
          Just (v, angle') -> rec (Set.insert v accum) angle'
  rec Set.empty m

localEnv :: AngleM a -> AngleM a
localEnv m = do
  env <- lift get
  result <- m
  lift $ put env
  return result

expandSet :: Set a -> AngleM a
expandSet s = Set.foldr (\a m -> return a `mplus` m) mzero s

runAngleM :: EDB -> IDB -> AngleM Value -> IO [((Value, Env), Unif)]
runAngleM edb idb m =
  let initialEnv = Map.empty
      initialUnif = (IntMap.empty,0)
      logicState = observeAllT (runStateT (runStateT (runReaderT (m >>= zonk) (DBs edb idb)) initialEnv) initialUnif)
  in logicState

debugPrint :: String -> AngleM ()
debugPrint msg = lift $ lift $ lift $ lift $ putStrLn msg

debugEnv :: AngleM ()
debugEnv = do
  env <- lift get
  debugPrint $ "Env: " ++ show env
  (unifMap,_) <- lift $ lift get
  debugPrint $ "Unif: " ++ show unifMap

-- Semantics

sem :: Angle -> AngleM Value
sem Unit = return VUnit
sem (Num n) = return (VNum n)
sem (Pair a1 a2) = VPair <$> sem a1 <*> sem a2
sem (Inl a) = VInl <$> sem a
sem (Inr a) = VInr <$> sem a
sem (Arr angles) = do
  values <- mapM sem angles
  return (VArr values)
sem Underscore = freshUnifVar
sem (Choice a1 a2) = sem a1 `mplus` sem a2
sem (Var x) = do
  mv <- lookupVar x
  case mv of
    Just v -> return v
    Nothing -> do
      v <- freshUnifVar
      setVar x v
sem (Pred name arg) = do
  iOrE <- lookupPred name
  case iOrE of
    Left angleDef -> do
      -- All predicates are considered recursive for simplicity
      -- It's correct, but inefficient
      p <- fixPoint name angleDef
      argValue <- sem arg
      match p argValue
    Right values -> do
      argValue <- sem arg
      vPred <- msum (map return values)
      match vPred argValue
sem (Seq a1 a2) = do
  _ <- sem a1
  sem a2
sem (Eq a1 a2) = do
  v1 <- sem a1
  v2 <- sem a2
  match v1 v2
sem (All a) = VSet <$> collectResults (sem a)
sem (Elements a) = do
  v <- sem a
  case v of
    VSet vs -> expandSet vs
    _       -> mzero
sem Never = mzero

fixPoint :: String -> Angle -> AngleM Value
fixPoint pred angle = do
  set <- collectResults $
          localEnv $
          localPred pred [] $
          sem angle >>= zonk
  let fixP prev = do
        res <- collectResults $
                localEnv $
                localPred pred (Set.toList prev) $
                sem angle >>= zonk
        if prev == res
          then return prev
          else fixP res
  vs <- fixP set
  expandSet vs

semiNaive :: String -> Angle -> AngleM Value
semiNaive pred angle = do
  set <- collectResults $
          localEnv $
          localPred pred [] $
          sem angle >>= zonk
  let deltaAngle = derivative pred angle
  let semiN prev delta = do
        res <- collectResults $
                localEnv $
                localPred pred (Set.toList prev) $
                localPred (pred ++ "Delta") (Set.toList delta) $
                sem deltaAngle >>= zonk
        let new = Set.difference res prev
        if Set.null new
          then return prev
          else semiN (Set.union prev new) new
  vs <- semiN set set
  expandSet vs

-- Matching and unification

zonk :: Value -> AngleM Value
zonk (VVar x) = do
  mv <- lookupUnif x
  case mv of
    Just v  -> zonk v
    Nothing -> return (VVar x)
zonk (VPair v1 v2) = VPair <$> zonk v1 <*> zonk v2
zonk (VInl v) = VInl <$> zonk v
zonk (VInr v) = VInr <$> zonk v
zonk (VArr vs) = VArr <$> mapM zonk vs
zonk (VSet vs) = VSet . Set.fromList <$> mapM zonk (Set.toList vs)
zonk v = return v

-- Unification of values
-- The (first) value is returned
match :: Value -> Value -> AngleM Value
match (VVar x) v = do
  mv <- lookupUnif x
  case mv of
    Just v' -> match v' v
    Nothing -> do
      setUnifVar x v
match v (VVar x) = match (VVar x) v
match (VPair v1 v2) (VPair v1' v2') =
  VPair <$>
  match v1 v1' <*>
  match v2 v2'
match (VInl v) (VInl v') = VInl <$> match v v'
match (VInr v) (VInr v') = VInr <$> match v v'
match (VArr vs) (VArr vs') =
  if length vs == length vs'
    then VArr <$> zipWithM match vs vs'
    else mzero
match (VSet vs) (VSet vs') =
  if Set.size vs == Set.size vs'
    then VSet . Set.fromList <$> zipWithM match (Set.toList vs) (Set.toList vs')
    else mzero
match v1 v2 =
  if v1 == v2
    then return v1
    else mzero

-- derivative

derivative :: String -> Angle -> Angle
derivative _ Unit = Never
derivative _ (Num _) = Never
derivative pred (Pair a1 a2) = Choice (Pair (derivative pred a1) a2) (Pair a1 (derivative pred a2)) -- TODO: is this correct?
derivative pred (Inl a) = Inl (derivative pred a)
derivative pred (Inr a) = Inr (derivative pred a)
derivative pred (Arr angles) = Arr (map (derivative pred) angles)
derivative _ Underscore = Never
derivative pred (Choice a1 a2) = Choice (derivative pred a1) (derivative pred a2)
derivative _ (Var _) = Never
derivative pred (Pred name arg) =
  if name == pred
    then Pred (name++"Delta") arg
    else Pred name (derivative pred arg) -- This can be optimized to `never` in some cases
derivative pred (Seq a1 a2) = Choice (Seq (derivative pred a1) a2) (Seq a1 (derivative pred a2))
derivative pred (Eq a1 a2) = Choice (Eq (derivative pred a1) a2) (Eq a1 (derivative pred a2)) -- TODO: is this correct?
derivative pred (All a) = All a -- TODO: can this be optimized?
derivative pred (Elements a) = Elements (derivative pred a)
derivative _ Never = Never

-- Simplification

simplify :: Angle -> Angle
simplify (Choice a1 a2) =
  let sa1 = simplify a1
      sa2 = simplify a2
  in if sa1 == sa2
      then sa1
      else case (sa1, sa2) of
             (Never, _) -> sa2
             (_, Never) -> sa1
             _          -> Choice sa1 sa2
simplify (Pair a1 a2) =
  case (simplify a1, simplify a2) of
    (Never, _) -> Never
    (_, Never) -> Never
    (sa1, sa2) -> Pair sa1 sa2
simplify (Inl a) =
  case simplify a of
    Never -> Never
    sa    -> Inl sa
simplify (Inr a) =
  case simplify a of
    Never -> Never
    sa    -> Inr sa
simplify (Arr angles) =
  let sas = map simplify angles
  in if Never `elem` sas
      then Never
      else Arr sas
simplify (Seq a1 a2) = seq (simplify a1) (simplify a2)
simplify (Eq a1 a2) = eq (simplify a1) (simplify a2)
simplify (Pred name arg) = Pred name (simplify arg)
simplify (All a) = case simplify a of
                      Elements sa -> sa
                      sa    -> All sa
simplify (Elements a) = case simplify a of
                           All sa -> sa
                           sa    -> Elements sa
simplify a = a

-- Smart constructors

eq :: Angle -> Angle -> Angle
eq (Var x) (Var y) =
  if x == y
    then Unit
    else Eq (Var x) (Var y)
eq (Var x) a2 = Eq (Var x) a2
eq a1 (Var y) = Eq a1 (Var y)
eq (Num n1) (Num n2) =
  if n1 == n2
    then Unit
    else Never
eq Unit Unit = Unit
eq (Inl a1) (Inl a2) = eq a1 a2
eq (Inr a1) (Inr a2) = eq a1 a2
eq (Pair a1 b1) (Pair a2 b2) = seq (eq a1 a2) (eq b1 b2)
eq (Arr a1s) (Arr a2s) =
  if length a1s == length a2s
    then foldr1 seq (zipWith eq a1s a2s)
    else Never
eq (Choice a b) c = Choice (eq a c) (eq b c)
eq a (Choice b c) = Choice (eq a b) (eq a c)
eq Underscore _ = Unit
eq _ Underscore = Unit
-- For predicates, we can be more aggressive and check if `arg` and `a` are
-- guaranteed to be unequal. Then the whole eq will fail.
eq (Pred name arg) a = Eq (Pred name arg) a
eq a (Pred name arg) = Eq a (Pred name arg)
eq (All a) b = Eq (All a) b
eq a (All b) = Eq a (All b)
eq (Elements a) b = Eq (Elements a) b
eq a (Elements b) = Eq a (Elements b)
eq (Seq a1 a2) b = seq a1 (eq a2 b)
eq a (Seq b1 b2) = seq b1 (eq a b2)
eq _ _ = Never -- We have to be really sure we cover all non-false cases above.

seq :: Angle -> Angle -> Angle
seq Never _ = Never
seq _ Never = Never
seq Unit a = a
seq (Pair a b) c = seq a (seq b c)
seq (Inl a) b = seq a b
seq (Inr a) b = seq a b
seq (Arr as) b = foldr seq b as
seq a1 a2 = Seq a1 a2

-- Tests

x,y,z :: Angle
x = Var "X"
y = Var "Y"
z = Var "Z"

edb1 :: EDB
edb1 = Map.fromList [("P",[VPair (VNum 1) (VNum 2), VPair (VNum 3) (VNum 4)])]
test1 :: IO Bool
test1 =
    ([((VNum 2,Map.fromList [("X",VVar 0)]),(IntMap.fromList [(0,VNum 2)],1))] ==) <$>
    runAngleM edb1 Map.empty (sem (Seq (Pred "P" (Pair (Num 1) (Var "X"))) (Var "X")))

-- Transitive closure
edb2 :: EDB
edb2 = Map.fromList [("P",[VPair (VNum 1) (VNum 2), VPair (VNum 2) (VNum 3), VPair (VNum 3) (VNum 4)])]
idb2 :: IDB
idb2 = Map.fromList [("R",Choice (Pred "P" (Pair x y)) (Seq (Pred "R" (Pair x z)) (Seq (Pred "P" (Pair z y)) (Pair x y))))]
test2 :: IO [((Value, Env), Unif)]
test2 = runAngleM edb2 idb2 (sem (Pred "R" (Pair (Num 1) y)))