-- free ambifibration from Section 5.3 of the paper

module Bif.Ambi where

import Data.Semigroup
import Data.List
import Data.Maybe

import Bif.Prover
import Bif.Test

-- represent order preserving maps f : m --> n as a list of (non-negative) integers xs
-- such that m = sum xs and n = length xs

newtype OP = OP { cnts :: [Int] }
  deriving (Show,Eq)

domOP, codOP :: OP -> Int
domOP = sum . cnts
codOP = length . cnts

idOP :: Int -> OP
idOP n = OP [1 | _ <- [0..n-1]]

-- generate all order-preserving maps f : m --> n
allOPs :: Int -> Int -> [OP]
allOPs m n
  | n == 0 = [OP [] | m == 0]
  | n > 0  = [OP (k : cnts f) | k <- [0..m], f <- allOPs (m-k) (n-1)]

-- sequential composition of two order-preserving maps f : m --> n and g : n --> p
seqOP :: OP -> OP -> OP
seqOP f g = OP (map sum (partBy (cnts g) (cnts f)))
  where
    partBy []     f = []
    partBy (c:cs) f = take c f : partBy cs (drop c f)

instance Semigroup OP where
  f <> g = f `seqOP` g

-- simplex category generators
sig :: Int -> Int -> OP
sig i n = OP $ [1 | _ <- [1..i]] ++ [2] ++ [1 | _ <- [i+1..n-1]]

del :: Int -> Int -> OP
del i n = OP $ [1 | _ <- [1..i]] ++ [0] ++ [1 | _ <- [i+1..n]]

-- ambisimplicial formulas

type AmbiFrm = Frm Int OP

-- generating all formulas in F_{n,k}

afrms :: Int -> Int -> [AmbiFrm]
afrms n k
  | n == k = [Atm n]
  | n > k  = [Pull (del i k) f | f <- afrms n (k+1), i <- [0..k]] ++
             [Push (sig i k) f | f <- afrms n (k+1), i <- [0..k-1]]
  | n < k  = []

-- prover for ambisimplicial formulas

ambiFPC :: FPCat Int OP
ambiFPC = FPC { idArr = idOP,
                dom = domOP,
                cod = codOP,
                factLE = factLE ,
                divLR = divLR , divL = divL , divR = divR }
  where
    -- the operations below are implemented by inefficient brute force search for now
    factLE (a,b) (c,d) = any (\e -> c == a <> e && b == e <> d) (allOPs m n)
      where
        m = codOP a
        n = codOP c
    divLR a f b = [g | g <- allOPs (codOP a) (domOP b), f == a <> g <> b]
    divL  a f   = [g | g <- allOPs (codOP a) (codOP f), f == a <> g]
    divR    f b = [g | g <- allOPs (domOP f) (domOP b), f == g <> b]

type AProof = Proof Int OP ()
aprove :: AmbiFrm -> OP -> AmbiFrm -> [AProof]
aprove = prove ambiFPC axiom
  where
    axiom m f n = [() | m == n && all (==1) (cnts f)]

-- poset F[n,k] of equivalence classes of ambisimplicial formulas,
-- represented as list of upsets [(s,[t | s <= t]) | s <- F[n,k]]
ambipos :: Int -> Int -> [(AmbiFrm,[AmbiFrm])]
ambipos n k = [(s,[t | t <- fnk, not $ null (aprove s (idOP k) t)]) | s <- fnk]
  where
    fnk = nubBy (\s t -> altFrm s == altFrm t) $ afrms n k

-- compute F[n,k] in a format suitable for input to Sagemath
ambipos_sage :: Int -> Int -> ([Int],[(Int,Int)])
ambipos_sage n k = (els, [(ix s,ix t) | s <- fnk, t <- fnk, not (null (aprove s (idOP k) t))])
  where
    fnk = nub (map altFrm $ afrms n k)
    els = [0..length fnk-1]
    dict = zip fnk els
    ix s = fromJust (lookup s dict)
    

tests1 = do
  expected [1,1,2,7,35,226,1787] "A014307" [length $ nubBy (\s t -> altFrm s == altFrm t) $ afrms n 0 | n <- [0..6]]
  expected [1,2,2,2,3,3,7] "partition of F{3,0} by upsets" (sort [length ts | (s,ts) <- ambipos 3 0])
  expected [1,2,2,2,2,2,2,3,3,3,3,3,3,3,3,5,5,5,5,7,7,7,7,9,9,9,9,10,10,10,10,14,14,14,35] "partition of F{4,0} by upsets" (sort [length ts | (s,ts) <- ambipos 4 0])

