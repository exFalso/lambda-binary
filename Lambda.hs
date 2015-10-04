{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
import           Control.Applicative
import           Control.Monad.List
import           Data.Bits
import           Data.List
import           Data.Monoid
import           Text.Printf

data SimpleLambda
  = SimpleLambda Integer LambdaTree
  deriving (Show)

data LambdaTree
  = Branch NestedLambdaTree NestedLambdaTree
  | Variable Integer
  deriving (Show)

data NestedLambdaTree
  = NestedBranch NestedLambdaTree NestedLambdaTree
  | NestedVariable Integer
  | NestedLambda SimpleLambda
  deriving (Show)

data Lambda
  = Lambda [String] Lambda
  | App [Lambda]
  | Var String

prettyLambda :: Lambda -> String
prettyLambda = prettyLambda' False
  where
    prettyLambda' :: Bool -> Lambda -> String
    prettyLambda' _ (Lambda vars body) = "(λ" <> intercalate " " vars <> ". " <> prettyLambda' False body <> ")"
    prettyLambda' insertParens (App terms) = (if insertParens then \a -> "(" <> a <> ")" else id) (intercalate " " (prettyLambda' True <$> terms))
    prettyLambda' _ (Var var) = var

allVariables :: [String]
allVariables = [] : liftA2 (flip (:)) allVariables ['a' .. 'z']

simpleLambdaToLambda :: SimpleLambda -> Lambda
simpleLambdaToLambda = simpleLambdaToLambda' (drop 1 allVariables)
  where

    simpleLambdaToLambda' vars (SimpleLambda offset tree) =
      let scope = getScope tree + fromIntegral offset
          body = simpleLambdaToLambda'' scope vars tree
      in if scope == 0 then body else Lambda (take scope vars) body

    simpleLambdaToLambda'' scope vars (Branch a b) = simpleLambdaToLambda''' scope vars (NestedBranch a b)
    simpleLambdaToLambda'' scope vars (Variable a) = simpleLambdaToLambda''' scope vars (NestedVariable a)

    simpleLambdaToLambda''' scope vars (NestedBranch a b) = App (collectApp scope vars a [simpleLambdaToLambda''' scope vars b])
    simpleLambdaToLambda''' _scope vars (NestedVariable a) = Var (vars !! fromInteger a)
    simpleLambdaToLambda''' scope vars (NestedLambda lam) = simpleLambdaToLambda' (drop scope vars) lam

    collectApp scope vars (NestedBranch a b) l = collectApp scope vars a (simpleLambdaToLambda''' scope vars b : l)
    collectApp scope vars nested l = simpleLambdaToLambda''' scope vars nested : l

    getScope :: LambdaTree -> Int
    getScope (Branch a b) = max (getScope' a) (getScope' b)
    getScope (Variable a) = fromInteger a + 1
    getScope' (NestedBranch a b) = max (getScope' a) (getScope' b)
    getScope' (NestedVariable a) = fromInteger a + 1
    getScope' NestedLambda{} = 0

data Result a
  = Done a [Bool]
  | More (BinParser a)
  deriving (Functor)

newtype BinParser a
  = BinParser ([Bool] -> Result a)

instance Functor BinParser where
  fmap f (BinParser g) = BinParser (fmap (fmap f) g)

instance Applicative BinParser where
  pure a = BinParser (\i -> Done a i)
  BinParser pf <*> BinParser pa =
    BinParser $ \i -> case pf i of
      Done f fRest -> case pa fRest of
        Done a aRest -> Done (f a) aRest
        More pa' -> More (f <$> pa')
      More pf' -> More (pf' <*> BinParser pa)

instance Monad BinParser where
  return = pure
  BinParser pa >>= f =
    BinParser $ \i -> case pa i of
      Done a aRest -> case f a of
        BinParser pb -> pb aRest
      More pa' -> More (pa' >>= f)

-- No Alternative instance, we cannot fail

next :: BinParser Bool
next = BinParser $ \case
  [] -> More next
  (a : rest) -> Done a rest


-- b - branch
-- v - variable
-- l - lambda

bvlParse :: BinParser SimpleLambda
bvlParse =
  SimpleLambda
    <$> natParse
    <*> treeParser
  where
    treeParser = next >>= \case
      False -> Branch <$> bvlParse' <*> bvlParse'
      True -> Variable <$> natParse
    bvlParse' :: BinParser NestedLambdaTree
    bvlParse' = next >>= \case
      False -> NestedBranch <$> bvlParse' <*> bvlParse'
      True -> next >>= \case
        False -> NestedVariable <$> natParse
        True -> NestedLambda <$> bvlParse

bvlSer :: SimpleLambda -> [Bool]
bvlSer (SimpleLambda n tree) =
  natSer n <> bvlSer' tree
  where
    bvlSer' (Variable i) = True : natSer i
    bvlSer' (Branch a b) = False : bvlSer'' a <> bvlSer'' b
    bvlSer'' (NestedVariable i) = True : False : natSer i
    bvlSer'' (NestedBranch na nb) = False : bvlSer'' na <> bvlSer'' nb
    bvlSer'' (NestedLambda lam) = True : True : bvlSer lam

vblParse :: BinParser SimpleLambda
vblParse =
  SimpleLambda
    <$> natParse
    <*> treeParser
  where
    treeParser = next >>= \case
      False -> Variable <$> natParse
      True -> Branch <$> vblParse' <*> vblParse'
    vblParse' :: BinParser NestedLambdaTree
    vblParse' = next >>= \case
      False -> NestedVariable <$> natParse
      True -> next >>= \case
        False -> NestedBranch <$> vblParse' <*> vblParse'
        True -> NestedLambda <$> vblParse

vblSer :: SimpleLambda -> [Bool]
vblSer (SimpleLambda n tree) =
  natSer n <> vblSer' tree
  where
    vblSer' (Variable i) = False : natSer i
    vblSer' (Branch a b) = True : vblSer'' a <> vblSer'' b
    vblSer'' (NestedVariable i) = False : natSer i
    vblSer'' (NestedBranch na nb) = True : False : vblSer'' na <> vblSer'' nb
    vblSer'' (NestedLambda lam) = True : True : vblSer lam

lbvParse :: BinParser SimpleLambda
lbvParse =
  SimpleLambda
    <$> natParse
    <*> treeParser
  where
    treeParser = next >>= \case
      False -> Variable <$> natParse
      True -> Branch <$> lbvParse' <*> lbvParse'
    lbvParse' :: BinParser NestedLambdaTree
    lbvParse' = next >>= \case
      False -> NestedLambda <$> lbvParse
      True -> next >>= \case
        False -> NestedBranch <$> lbvParse' <*> lbvParse'
        True -> NestedVariable <$> natParse

lbvSer :: SimpleLambda -> [Bool]
lbvSer (SimpleLambda n tree) =
  natSer n <> lbvSer' tree
  where
    lbvSer' (Variable i) = False : natSer i
    lbvSer' (Branch a b) = True : lbvSer'' a <> lbvSer'' b
    lbvSer'' (NestedVariable i) = True : True : natSer i
    lbvSer'' (NestedBranch na nb) = True : False : lbvSer'' na <> lbvSer'' nb
    lbvSer'' (NestedLambda lam) = False : lbvSer lam

natSer :: Integer -> [Bool]
natSer 0 = [False]
natSer i = True : listSer (tail (natSer' [] i))
  where
    listSer [] = [False]
    listSer (a : as) = True : a : listSer as
    natSer' acc 0 = acc
    natSer' acc n = natSer' ((n `mod` 2 == 1) : acc) (n `div` 2)


natParse :: BinParser Integer
natParse = do
  next >>= \case
    False -> pure 0
    True -> natParse'' 1

  where
    natParse' acc = next >>= \case
      False -> natParse'' (acc `shift` 1)
      True -> natParse'' ((acc `shift` 1) + 1)
    natParse'' acc = next >>= \case
      False -> pure acc
      True -> natParse' acc

nextGen :: [([Bool], Gen a)] -> [([Bool], Gen a)]
nextGen gen = do
  bi <- [False, True]
  gen >>= \case
    (_, GenDone{}) -> []
    (acc, GenMore (BinParser p)) -> resultToGen $ p [bi]
      where
        resultToGen (Done a _) = [(bi : acc, GenDone a (reverse $ bi : acc))]
        resultToGen (More m) = [(bi : acc, GenMore m)]

binsLambdas :: BinParser t -> [([Bool], t)]
binsLambdas parser = getBinsDones . snd =<< concat (gens parser)

getDones :: Gen t -> [t]
getDones (GenDone a _) = [a]
getDones _ = []

getBinsDones :: Gen t -> [([Bool], t)]
getBinsDones (GenDone a b) = [(b, a)]
getBinsDones _ = []

gens :: BinParser a -> [[([Bool], Gen a)]]
gens parser = iterate nextGen [([], GenMore parser)]


data Gen a
  = GenDone a [Bool]
  | GenMore (BinParser a)

instance Show a => Show (Gen a) where
  show (GenDone a b) = show a <> " ::: " <> showBin b
  show GenMore{} = "More..."

showBin :: [Bool] -> String
showBin [] = ""
showBin (False : rest) = '0' : showBin rest
showBin (True : rest) = '1' : showBin rest

runParse :: BinParser a -> [Bool] -> Maybe a
runParse (BinParser p) i = case p i of
  Done a _ -> Just a
  _ -> Nothing

main :: IO ()
main = do
  let parsers =
        [ ("vbl", vblParse, vblSer)
        , ("bvl", bvlParse, bvlSer)
        , ("lbv", lbvParse, lbvSer)
        ]

  forM_ parsers $ \(parserName, parser, serialize) -> do
    let parses = gens parser
    printf "%s:\n" parserName
    forM_ [1::Int .. 20] $ \b -> do
      let nDones = length $ getDones =<< concat (map (snd <$>) (take b parses))
          nNumbers = (1::Int) `shift` b
      printf " %2d: %5.2f%%\n" b (fromIntegral nDones * 100 / fromIntegral nNumbers :: Double)
    printf "\n"

    printf "First 50 lambdas:\n"
    forM_ (take 50 $ binsLambdas parser) $ \(b, l) ->
      printf " %12s: %s\n" (showBin b) (prettyLambda (simpleLambdaToLambda l))

    printf "\n"

    forM_ [("Y combinator", y), ("Small Y combinator", smallY)] $ \(desc, term) -> do
      printf "%s:\n" desc
      let bin = serialize term
      printf " %50s[%d]: %s\n" (showBin bin) (length bin) (prettyLambda (simpleLambdaToLambda term))

y :: SimpleLambda
y = SimpleLambda 0 (Branch (NestedBranch (NestedLambda (SimpleLambda 0 (Branch (NestedVariable 0) (NestedBranch (NestedVariable 1) (NestedVariable 1))))) (NestedVariable 0)) (NestedBranch (NestedLambda (SimpleLambda 0 (Branch (NestedVariable 0) (NestedBranch (NestedVariable 1) (NestedVariable 1))))) (NestedVariable 0)))

smallY :: SimpleLambda
smallY = SimpleLambda 0 (Branch (NestedLambda (SimpleLambda 0 (Branch (NestedVariable 0) (NestedVariable 0)))) (NestedBranch (NestedLambda (SimpleLambda 0 (Branch (NestedVariable 0) (NestedBranch (NestedVariable 1) (NestedVariable 1))))) (NestedVariable 0)))
