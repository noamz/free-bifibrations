-- visualization routines used for the diagrams in Sections 5.1-5.2 of the paper;
-- currently a horrible mess of spaghetti code, should be cleaned up and unified with Bif.AmbiDiags

module Bif.PTreeDiags where

import Bif.Prover
import Bif.PTree

import Text.Printf (printf)
import Data.Semigroup

delta :: TreeFrm -> Int
delta (Atm _) = 0
delta (Push f s) = delta s + getSum f
delta (Pull f s) = delta s - getSum f

proof_stack :: TProof -> String
proof_stack (Done _ _) = "|[alias=l0]| 0 \\ar[r,equals] \\& |[alias=r0]| 0 \n"
proof_stack (Step (s,f,t) rule pf) =
  proof_stack pf ++ "\\\\ " ++ alias "l" ++ show (delta s) ++ leftArrow rule ++ 
  "\\ar[r" ++ (if f == 0 then ",equals" else "") ++ "] \\& " ++
  alias "r" ++ show (delta t) ++ rightArrow rule ++ "\n"
  where
    row = length (toSequents pf)
    alias str = "|[alias=" ++ str ++ show row ++ "]|"
    leftArrow (LFoc x) = "\\ar[u]"
    leftArrow (LRFoc x _) = "\\ar[u]"
    leftArrow (Invert (Just x) _) = "\\ar[u,<-]"
    leftArrow _ = "\\ar[u,equals]"
    rightArrow (RFoc x) = "\\ar[u,<-]"
    rightArrow (LRFoc _ x) = "\\ar[u,<-]"
    rightArrow (Invert _ (Just x)) = "\\ar[u]"
    rightArrow _ = "\\ar[u,equals]"

proof_rules :: TProof -> String
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

proof_chords :: String -> TProof -> String
proof_chords color (Done _ _) = ""
proof_chords color (Step (s,Sum f,t) rule pf) =
  proof_chords color pf ++
  leftChords rule ++ middleChords rule ++ rightChords rule
  where
    (_,Sum g,_) = proofOf pf
    row = length (toSequents pf)
    drawCmd dir from to = "\\draw[draw=" ++ color ++ ", draw opacity=0.5, line width=1mm," ++ dir ++ "] ($" ++ from ++ "$) to ($" ++ to ++ "$);\n"
    ratio i j = printf "%.2f" ((fromIntegral i :: Float) / (fromIntegral j :: Float))
    colPt side row i x = "(" ++ side ++ show row ++ ")!" ++ ratio i (x+1) ++ "!(" ++ side ++ show (row-1) ++ ")"
    rowPt row i f = "(l" ++ show row ++ ")!" ++ ratio i (f+1) ++ "!(r" ++ show row ++ ")"
    leftChords (LFoc (Sum x)) = do
      i <- [1..(-x)]
      drawCmd "out=90,in=0" (rowPt row i f) (colPt "l" row i (-x))
    leftChords (LRFoc (Sum x) _) = do
      i <- [1..(-x)]
      drawCmd "out=90,in=0" (rowPt row i f) (colPt "l" row i (-x))
    leftChords (Invert (Just (Sum x)) _) = do
      i <- [1..x]
      drawCmd "out=0,in=-90" (colPt "l" row (x-i+1) x) (rowPt (row-1) i g)
    leftChords _ = ""
    rightChords (RFoc (Sum x)) = do
      i <- [1..x]
      drawCmd "out=90,in=180" (rowPt row (f-i+1) f) (colPt "r" row i x)
    rightChords (LRFoc _ (Sum x)) = do
      i <- [1..x]
      drawCmd "out=90,in=180" (rowPt row (f-i+1) f) (colPt "r" row i x)
    rightChords (Invert _ (Just (Sum x))) = do
      i <- [1..(-x)]
      drawCmd "out=180,in=-90" (colPt "r" row (-x-i+1) (-x)) (rowPt (row-1) (g-i+1) g)
    rightChords _ = ""
    middleChords (LFoc (Sum x)) = do
      i <- [1..(f+x)]
      drawCmd "out=90,in=-90" (rowPt row (i-x) f) (rowPt (row-1) i g)
    middleChords (LRFoc (Sum x) (Sum y)) = do
      i <- [1..(f+x-y)]
      drawCmd "out=90,in=-90" (rowPt row (i-x) f) (rowPt (row-1) i g)
    middleChords (RFoc (Sum x)) = do
      i <- [1..(f-x)]
      drawCmd "out=90,in=-90" (rowPt row i f) (rowPt (row-1) i g)
    middleChords (Invert mx my) = do
      i <- [1..f]
      drawCmd "out=90,in=-90" (rowPt row i f) (rowPt (row-1) (maybe 0 getSum mx + i) g)
    
tikzcdProof :: String -> TProof -> String
tikzcdProof color proof = "\\begin{tikzcd}[ampersand replacement=\\&,row sep=1cm,execute at end picture = { \n" ++ proof_chords color proof ++ "}\n ]\n" ++ proof_stack proof ++ proof_rules proof ++ "\\end{tikzcd}\n"

tikzcdProofs :: Bool -> String -> [TProof] -> String -> IO ()
tikzcdProofs standalone color proofs fpath =
  writeFile fpath $
  header ++ 
  (if length proofs == 1 then tikzcdProof color (proofs !! 0) else concatMap (\proof -> "\\resizebox{!}{7cm}{" ++ tikzcdProof color proof ++ "}\n") proofs) ++
  footer
  where
    header = if not standalone then "" else 
      "\\documentclass{standalone}\n" ++
      "\\usepackage{amsmath}\n" ++
      "\\usepackage{tikz-cd}\n" ++
      "\\usetikzlibrary{calc,positioning,decorations.markings,decorations.pathreplacing,patterns,hobby,backgrounds}\n" ++
      "\\input macros\n" ++ 
      "\\definecolor{frenchblue}{rgb}{0.0, 0.45, 0.73}\n" ++
      "\\definecolor{persianred}{rgb}{0.8, 0.2, 0.2}\n" ++
      "\\begin{document}\n"
    footer = if not standalone then "" else
      "\\end{document}\n"

-- generating LaTeX sequent proof output

latexFrm :: TreeFrm -> String
latexFrm (Push f s) = "f^{+" ++ show f ++ "}" ++ latexFrm s
latexFrm (Pull f s) = "f^{-" ++ show f ++ "}" ++ latexFrm s
latexFrm (Atm _) = "\\ast"

latexSequent :: TSequent -> String
latexSequent (s,f,t) = latexFrm s ++ " \\vdashf{f^{" ++ show f ++ "}} " ++ latexFrm t

latexProof :: TProof -> String
latexProof (Done seq _) = "\\inferrule* { }{ " ++ latexSequent seq ++ " }\n"
latexProof (Step seq rule pf) = "\\inferrule* { \n" ++ latexProof pf ++ " } { " ++ latexSequent seq ++ " }\n"

-- tikz for examples in paper
base = "diagrams/"

example1 = do
  mapM_ (\(i,pf) -> tikzcdProofs False "violet" [pf] (base ++ "ord22_" ++ show i ++ ".tex")) (zip [0..] (tprove (ord 2) 0 (ord 2)))

example2 = do
  mapM_ (\(i,pf) -> tikzcdProofs False (if i == 1 then "frenchblue" else if i == 6 then "persianred" else "lightgray") [pf] (base ++ "tree_morphism_" ++ show i ++ ".tex")) (zip [0..] (tprove treeS 0 treeT))

example3 = do
  mapM_ (\(i,pf) -> tikzcdProofs False "violet" [pf] (base ++ "walk_" ++ show i ++ ".tex")) (zip [0..] (tprove (wordFrm [-1,3,-2,1]) 0 (wordFrm [-1,1,-1,2])))
  
tikzExamples :: IO ()
tikzExamples = do
  example1
  example2
  example3

tikzTrees :: TreeFrm -> TreeFrm -> String -> IO ()
tikzTrees src tgt fname = do
  tikzcdProofs True "violet" (tprove src 0 tgt) (base ++ fname ++ ".tex")

-- to generate a tex file with all morphisms between a pair of trees:
-- tikzTrees treeT treeU' "out"

