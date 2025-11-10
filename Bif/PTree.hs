module Bif.PTree where

import Data.Semigroup

import Bif.Prover
import Bif.Test

type TreeFrm = Frm () (Sum Int)

-- prover for tree formulas
treeFPC :: FPCat () (Sum Int)
treeFPC = FPC { dom = (\_ -> ()), cod = (\_ -> ()),
                idArr = (\_ -> Sum 0),
                factLE = factLE ,
                divLR = divLR , divL = divL , divR = divR }
  where
    axiom () (Sum n) () = [() | n == 0]
    domOb _ = ()
    codOb _ = ()
    idArr _ = Sum 0
    factLE (a,b) (c,d) = a <= c && d <= b && a+b == c+d
    divLR a m b = [-a+m-b | m >= a+b]
    divL  a m   = [-a+m   | m >= a]
    divR    m b = [   m-b | m >= b]

type TSequent = Sequent () (Sum Int)
type TProof = Proof () (Sum Int) ()

tprove :: TreeFrm -> Int -> TreeFrm -> [TProof]
tprove s n t = prove treeFPC axiom s (Sum n) t
  where
    axiom () (Sum n) () = [() | n == 0]

-- generate all right-to-left dyck words
dwords :: Int -> [[Int]]
dwords n
  | n == 0 = [[]]
  | n > 0  = [-1 : w1 ++ 1 : w2 | k <- [0..n-1], w1 <- dwords k, w2 <- dwords (n-1-k)]

-- convert a word to a bifibrational formula
wordFrm :: [Int] -> TreeFrm
wordFrm = foldr (\step t -> if step > 0 then Push (Sum step) t
                                        else Pull (Sum (-step)) t) (Atm ())

-- the unique height-1 dyck path with 2n steps = unique n-edge, height-1 tree,
-- which behaves like the n'th ordinal
ord :: Int -> TreeFrm
ord n = wordFrm $ concat $ replicate n [-1,1]

-- the unique height-n dyck path with 2n steps = unique n-edge, height-n tree
line :: Int -> TreeFrm
line n = wordFrm [-n,n]

-- run some tests, generating some sequences

inseq :: TreeFrm -> [Int]
inseq t = [length $ concat [tprove u 0 t | u <- map wordFrm (dwords n)] | n <- [0..]]

outseq :: TreeFrm -> [Int]
outseq t = [length $ concat [tprove t 0 u | u <- map wordFrm (dwords n)] | n <- [0..]]

tests1 = do
  expected [1,3,10,35,126,462,1716,6435] "A001700"
           [length $ tprove (ord n) 0 (ord n) | n <- [1..8]] 
  expected [[1],[1,1],[1,2,3],[1,3,6,10],[1,4,10,20,35],[1,5,15,35,70,126]] "A059481"
           [[length $ tprove (ord m) 0 (ord n) | m <- [0..n]] | n <- [0..5]]
  expected [1,1,3,9,29,98,343,1232,4514,16803,63367] "not in OEIS"
           [length $ concat [tprove u 0 v | k <- [0..n], u <- map wordFrm (dwords k), v <- map wordFrm (dwords (n-k))] | n <- [0..10]]

tests2 = do
  expected [0,0,1,6,27,110,429,1638,6188,23256,87210] "A003517"
           (take 11 $ outseq $ wordFrm [-2,1,-1,2])
  expected [0,0,1,6,27,110,429,1638,6188,23256,87210] "A003517"
           (take 11 $ outseq $ wordFrm [-2,2,-1,1])
  expected [0,0,1,7,35,154,637,2548,9996,38760,149226] "A000588"
           (take 11 $ outseq $ wordFrm [-2,1,-1,1,-1,2])
  expected [0,0,1,6,28,119,483,1911,7448,28764,110466] "A026014"
           (take 11 $ outseq $ wordFrm [-2,2,-2,2])

tests3 = do
  expected [1,2,4,8,16,32,64,128,256,512,1024] "2^n"
           (take 11 $ inseq $ wordFrm [-2,2,-1,1])
  expected [1,1,3,8,20,48,112,256,576,1280,2816] "A001792 with leading 1"
           (take 11 $ inseq $ wordFrm [-2,1,-1,2])

tests4 = do
  expected [0,0,0,0,0,1,11,77,440,2244,10659,48279,211508] "A000589"
           (take 13 $ outseq (line 5))
  expected [0,0,0,0,0,0,1,13,104,663,3705,19019,92092] "A000590"
           (take 13 $ outseq (line 6))

-- trees S and T from (5.1) in Section 5.2

treeS :: TreeFrm
treeS = wordFrm [-2,2,-1,1,-2,1,-1,2]
treeT :: TreeFrm
treeT = wordFrm [-3,2,-1,2,-1,1,-2,2]

test_example = do
  expected 11 "# morphisms S -> T" (length $ tprove treeS 0 treeT)

