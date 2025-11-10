-- visualization routines used for the diagrams in Section 5.3 of the paper;
-- currently a horrible mess of spaghetti code, should be cleaned up and unified with Bif.PTreesDiags

module Bif.AmbiDiags where

import Bif.Prover
import Bif.Ambi

import Data.List

codAFrm :: AmbiFrm -> Int
codAFrm (Atm n) = n
codAFrm (Push f _) = codOP f
codAFrm (Pull f _) = domOP f

name_OP :: Bool -> OP -> String
name_OP sid f = if sid && all (==1) (cnts f) then "equals" else "\"{" ++ intercalate "," (map show (cnts f)) ++ "}\""

proof_stack :: AProof -> String
proof_stack (Done (m,f,n) _) = "|[alias=l0]| " ++ show m ++ " \\ar[r," ++ name_OP True f ++ "] \\& |[alias=r0]| " ++ show n ++ " \n"
proof_stack (Step (s,f,t) rule pf) =
  proof_stack pf ++ "\\\\ " ++ alias "l" ++ show (codAFrm s) ++ leftArrow rule ++ 
  "\\ar[r," ++ name_OP True f ++ "] \\& " ++
  alias "r" ++ show (codAFrm t) ++ rightArrow rule ++ "\n"
  where
    row = length (toSequents pf)
    alias str = "|[alias=" ++ str ++ show row ++ "]|"
    leftArrow (LFoc x) = "\\ar[u,tail," ++ name_OP False x ++ "]"
    leftArrow (LRFoc x _) = "\\ar[u,tail," ++ name_OP False x ++ "]"
    leftArrow (Invert (Just x) _) = "\\ar[u,<-,twoheadleftarrow," ++ name_OP False x ++"]"
    leftArrow _ = "\\ar[u,equals]"
    rightArrow (RFoc x) = "\\ar[u,<-,twoheadleftarrow," ++ name_OP False x ++ "']"
    rightArrow (LRFoc _ x) = "\\ar[u,<-,twoheadleftarrow," ++ name_OP False x ++ "']"
    rightArrow (Invert _ (Just x)) = "\\ar[u,tail," ++ name_OP False x ++ "']"
    rightArrow _ = "\\ar[u,equals]"

proof_rules :: AProof -> String
proof_rules (Done _ _) = ""
proof_rules (Step (s,f,t) rule pf) =
  proof_rules pf ++
  "\\arrow[gray,phantom,from=" ++ show row ++ "-1,to=" ++ show (row+1) ++ "-2," ++ ruleString rule ++ "]\n"
  where
    row = length (toSequents pf)
    ruleString (LFoc _) = "\"\\pull \\Lsym\""
    ruleString (LRFoc _ _) = "\"\\pull \\Lsym \\push \\Rsym\""
    ruleString (RFoc _) = "\"\\push \\Rsym\""
    ruleString (Invert mx my) = "\"" ++ maybe "" (const "\\push \\Lsym") mx ++ maybe "" (const "\\pull \\Rsym") my ++ "\""

tikzcdProof :: AProof -> String
tikzcdProof proof = "\\begin{tikzcd}[ampersand replacement=\\&,row sep=1cm]\n" ++ proof_stack proof ++ proof_rules proof ++ "\\end{tikzcd}\n"

tikzcdProofs :: Bool -> [AProof] -> String -> IO ()
tikzcdProofs standalone proofs fpath =
  writeFile fpath $
  header ++ 
  (if length proofs == 1 then tikzcdProof (proofs !! 0) else concatMap (\proof -> "\\resizebox{!}{7cm}{" ++ tikzcdProof proof ++ "}\n") proofs) ++
  footer
  where
    header = if not standalone then "" else 
      "\\documentclass{standalone}\n" ++
      "\\usepackage{amsmath}\n" ++
      "\\usepackage{tikz-cd}\n" ++
      "\\usetikzlibrary{calc,positioning,decorations.markings,decorations.pathreplacing,patterns,hobby,backgrounds}\n" ++
      "\\input macros\n" ++ 
      "\\begin{document}\n"
    footer = if not standalone then "" else
      "\\end{document}\n"
