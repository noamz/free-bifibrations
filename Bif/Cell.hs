-- simple example involving 2-cells

module Bif.Cell where

import Data.Semigroup
import Data.List

import Bif.Frm
import Bif.Prover

data Ob = ObA | ObB | ObC
  deriving (Show,Eq)
instance Semigroup Ob where
  x <> y = x

data Edge = A_e | A_f | A_g | A_h
  deriving (Show,Eq)
type Arr = (Ob,[Edge])

domArr, codArr :: Arr -> Ob
domArr (x,path) = x
codArr (x,path)
  | null path = x
  | otherwise =
    case last path of
      A_e -> ObA
      A_f -> ObB
      A_g -> ObC
      A_h -> ObC

data Cell = Alpha | Beta
  deriving (Show,Eq)

cellFPC :: FPCat Ob Arr Cell
cellFPC = FPC { idArr = \x -> (x,[]),
                dom = domArr,
                cod = codArr,
                factLE = factLE ,
                divLR = divLR , divL = divL , divR = divR , cell }
  where
    factLE ((_,a),(_,b)) ((_,c),(_,d)) = d `elem` (tails b)
    divLR (x,a) (_,f) (y,b) = [(codArr (x,a), g) | let m = length a, a == take m f, let n = length b, b == reverse (take n (reverse f)), let g = reverse (drop n (reverse (drop m f)))]
    divL  (x,a) (_,f)   = [(codArr (x,a), g) | let m = length a, a == take m f, let g = drop m f]
    divR  (x,f) (_,b) = [(x,g) | let n = length b, b == reverse (take n (reverse f)), let g = reverse (drop n (reverse f))]
    cell (ObA, [A_f,A_g]) = [((ObA, [A_e,A_h]), Alpha)]
    cell (ObA, [A_h]) = [((ObA, [A_f,A_g]), Beta)]
    cell _ = []

prover :: Arr -> Frm Ob Arr -> Arr -> Frm Ob Arr -> [Proof Ob Arr Cell ()]
prover g = prove cellFPC (axiom g)
  where
    axiom g a f b = [() | f == g, domArr f == a, codArr f == b]

tests1 = do
  let ders = prover (ObA, [A_e]) (Pull (ObA, [A_f]) $ Push (ObA, [A_f]) $ Atm ObA)
                (ObA, [])
                (Pull (ObA, [A_h]) $ Push (ObA, [A_h]) $ Atm ObA)
  putStrLn (show (length ders) ++ " derivation(s):")
  print ders
  

