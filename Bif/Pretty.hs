-- pretty printing routines

module Bif.Pretty where

import Data.List (intercalate)

import Bif.Frm
import Bif.Prover

-- pretty printing of formulas
prettyFrm :: (ob -> String) -> (arr -> String) -> Frm ob arr -> String
prettyFrm prOb prArr (Atm x)    = prOb x
prettyFrm prOb prArr (Push f s) = prArr f ++ "+ " ++ prettyFrm prOb prArr s
prettyFrm prOb prArr (Pull f s) = prArr f ++ "- " ++ prettyFrm prOb prArr s

-- pretty printing of sequents
prettySequent :: (ob -> String) -> (arr -> String) -> Sequent ob arr -> String
prettySequent prOb prArr (s,f,t) = prettyFrm prOb prArr s ++ " ==" ++ prArr f ++ "==> " ++ prettyFrm prOb prArr t

-- pretty printing of list of sequents
prettySequents :: (ob -> String) -> (arr -> String) -> [Sequent ob arr] -> String
prettySequents prOb prArr = intercalate "\n---------\n" . map (prettySequent prOb prArr)

-- pretty printing of proofs in simplified form, as lists of sequents
prettyProof :: (ob -> String) -> (arr -> String) -> Proof ob arr cell ax -> String
prettyProof prOb prArr = prettySequents prOb prArr . reverse . toSequents
