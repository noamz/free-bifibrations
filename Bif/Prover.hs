module Bif.Prover where

import Bif.Frm

-- sequents and proof rules
type Sequent ob arr = (Frm ob arr, arr, Frm ob arr)

data Rule arr cell = Invert (Maybe arr) (Maybe arr)
              | LFoc arr | LRFoc arr arr | RFoc arr
              | Cell cell  -- experimental support for 2-cells
  deriving (Show,Eq)

data Proof ob arr cell ax = Done (Sequent ob arr) ax | Step (Sequent ob arr) (Rule arr cell) (Proof ob arr cell ax)
  deriving (Show,Eq)

proofOf :: Proof ob arr cell ax -> Sequent ob arr
proofOf (Done seq _)   = seq
proofOf (Step seq _ _) = seq

toSequents :: Proof ob arr cell ax -> [Sequent ob arr]
toSequents (Done seq _) = [seq]
toSequents (Step seq rule ps) = seq : toSequents ps

-- prover states

data IState = LI | RI | BotI
  deriving (Show,Eq)
data FState arr = LF (arr,arr) | RF (arr,arr) | BotF
  deriving (Show,Eq)

i2f :: IState -> (arr,arr) -> FState arr
i2f LI   f = LF f
i2f RI   f = RF f
i2f BotI f = BotF

isLF :: FState arr -> ((arr,arr) -> Bool) -> Bool
isLF (LF x) k = k x
isLF _      k = False

isRF :: FState arr -> ((arr,arr) -> Bool) -> Bool
isRF (RF x) k = k x
isRF _      k = False

-- extra structure on objects and arrows needed by the prover, besides composition (which comes from
-- the instance of Semigroup and is notated "<>", but we notate ";" when explaining the functions below)
data FPCat ob arr cell = FPC {
  dom, cod :: arr -> ob ,
  idArr :: ob -> arr ,
  factLE :: (arr,arr) -> (arr,arr) -> Bool ,
  -- factLE (a,b) (c,d)  <=>  exists u. c = (a;u) /\ b = (u;d)
  divLR :: arr -> arr -> arr -> [arr] ,
  -- g in divLR sigma f tau <=> f = sigma;g;tau
  divL :: arr -> arr -> [arr] ,
  -- g in divL sigma f <=> f = sigma;g
  divR :: arr -> arr -> [arr] ,
  -- g in divR f tau <=> f = g;tau
  cell :: arr -> [(arr,cell)]
  -- (g,alpha) in cell f <=> nonidentity 2-cell alpha : g => f
  }

-- inversion mode proofs of s ==f==> t where s and t are strictly alternating formulas
iprove :: Semigroup arr => FPCat ob arr cell -> (ob -> arr -> ob -> [ax]) -> IState -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr cell ax]
iprove fpc axiom BotI (s@(Push pi s')) f (t@(Pull rho t')) =
  [Step (s,f,t) (Invert (Just pi) (Just rho)) p | p <- cprove fpc axiom BotF s' (pi <> f <> rho) t']
iprove fpc axiom qi (s@(Push pi s')) f t = 
  [Step (s,f,t) (Invert (Just pi) Nothing) p | p <- cprove fpc axiom (qi `i2f` (pi,f)) s' (pi <> f) t]
iprove fpc axiom qi s f (t@(Pull rho t')) = 
  [Step (s,f,t) (Invert Nothing (Just rho)) p | p <- cprove fpc axiom (qi `i2f` (f,rho)) s (f <> rho) t']
iprove fpc axiom BotI s f t = cprove fpc axiom BotF s f t
iprove fpc axiom LI   s f t = cprove fpc axiom (LF (idArr fpc (dom fpc f),f)) s f t
iprove fpc axiom RI   s f t = cprove fpc axiom (RF (f,idArr fpc (cod fpc f))) s f t

-- "cell mode" for interleaving a 2-cell (experimental)
cprove :: Semigroup arr => FPCat ob arr cell -> (ob -> arr -> ob -> [ax]) -> FState arr -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr cell ax]
cprove fpc axiom qf s f t = fprove fpc axiom qf s f t ++
                            [Step (s,f,t) (Cell alpha) p | (g,alpha) <- cell fpc f, p <- fprove fpc axiom BotF s g t]

-- focus mode proofs of s ==f==> t where s and t are strictly alternating formulas
fprove :: Semigroup arr => FPCat ob arr cell -> (ob -> arr -> ob -> [ax]) -> FState arr -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr cell ax]
fprove fpc axiom qf (s@(Atm x)) f (t@(Atm y)) = 
  [Done (s,f,t) ax | ax <- axiom x f y]
fprove fpc axiom qf (s@(Pull sigma s')) f (t@(Push tau t')) = 
  let (<=) = factLE fpc in
  [Step (s,f,t) (LRFoc sigma tau) p |
   g <- divLR fpc sigma f tau,
   not (isLF qf (\(pi,f')  -> (pi,f') <= (sigma<>g,tau))) &&
   not (isRF qf (\(f',rho) -> (sigma,g<>tau) <= (f',rho))),
   p <- iprove fpc axiom BotI s' g t'] ++
  [Step (s,f,t) (LFoc sigma) p | 
   g <- divL fpc sigma f,
   not (isRF qf (\(f',rho) -> (sigma,g) <= (f',rho))),
   p <- iprove fpc axiom LI s' g t] ++
  [Step (s,f,t) (RFoc tau) p | 
   g <- divR fpc f tau,
   not (isLF qf (\(pi,f') -> (pi,f') <= (g,tau))),
   p <- iprove fpc axiom RI s g t']
fprove fpc axiom qf (s@(Pull sigma s')) f t =
  let (<=) = factLE fpc in
  [Step (s,f,t) (LFoc sigma) p | 
   g <- divL fpc sigma f,
   not (isRF qf (\(f',rho) -> (sigma,g) <= (f',rho))),
   p <- iprove fpc axiom LI s' g t]
fprove fpc axiom qf s f (t@(Push tau t')) =
  let (<=) = factLE fpc in
  [Step (s,f,t) (RFoc tau) p | 
   g <- divR fpc f tau,
   not (isLF qf (\(pi,f') -> (pi,f') <= (g,tau))),
   p <- iprove fpc axiom RI s g t']

-- generate all proofs of s ==f==> t where s and t are bifibrational formulas
prove :: Semigroup arr => FPCat ob arr cell -> (ob -> arr -> ob -> [ax]) -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr cell ax]
prove fpc axiom s f t = iprove fpc axiom BotI (altFrm s) f (altFrm t)
