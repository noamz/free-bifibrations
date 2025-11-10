module Bif.Prover where

-- syntax of bifibrational formulas
data Frm ob arr = Atm ob | Push arr (Frm ob arr) | Pull arr (Frm ob arr)
  deriving (Show,Eq)

-- normalize a bifibrational formula to a strictly alternating bifibrational formula
altFrm :: Semigroup arr => Frm ob arr -> Frm ob arr
altFrm (Atm x)    = Atm x
altFrm (Push f s) = case altFrm s of
                      Push f' s' -> Push (f' <> f) s'
                      s'         -> Push f s'
altFrm (Pull g t) = case altFrm t of
                      Pull g' t' -> Pull (g <> g') t'
                      t'         -> Pull g t'

-- sequents and proof rules
type Sequent ob arr = (Frm ob arr, arr, Frm ob arr)

data Rule arr = Invert (Maybe arr) (Maybe arr)
              | LFoc arr | LRFoc arr arr | RFoc arr
  deriving (Show,Eq)

data Proof ob arr ax = Done (Sequent ob arr) ax | Step (Sequent ob arr) (Rule arr) (Proof ob arr ax)
  deriving (Show,Eq)

proofOf :: Proof ob arr ax -> Sequent ob arr
proofOf (Done seq _)   = seq
proofOf (Step seq _ _) = seq

toSequents :: Proof ob arr ax -> [Sequent ob arr]
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

-- extra structure on objects and arrows needed by the prover (besides composition = Semigroup)
data FPCat ob arr = FPC {
  dom, cod :: arr -> ob ,
  idArr :: ob -> arr ,
  factLE :: (arr,arr) -> (arr,arr) -> Bool ,
  divLR :: arr -> arr -> arr -> [arr] ,
  divL :: arr -> arr -> [arr] ,
  divR :: arr -> arr -> [arr]
  }

-- inversion mode proofs of s ==f==> t where s and t are strictly alternating formulas
iprove :: Semigroup arr => FPCat ob arr -> (ob -> arr -> ob -> [ax]) -> IState -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr ax]
iprove fpc axiom BotI (s@(Push pi s')) f (t@(Pull rho t')) =
  [Step (s,f,t) (Invert (Just pi) (Just rho)) p | p <- fprove fpc axiom BotF s' (pi <> f <> rho) t']
iprove fpc axiom qi (s@(Push pi s')) f t = 
  [Step (s,f,t) (Invert (Just pi) Nothing) p | p <- fprove fpc axiom (qi `i2f` (pi,f)) s' (pi <> f) t]
iprove fpc axiom qi s f (t@(Pull rho t')) = 
  [Step (s,f,t) (Invert Nothing (Just rho)) p | p <- fprove fpc axiom (qi `i2f` (f,rho)) s (f <> rho) t']
iprove fpc axiom BotI s f t = fprove fpc axiom BotF s f t
iprove fpc axiom LI   s f t = fprove fpc axiom (LF (idArr fpc (dom fpc f),f)) s f t
iprove fpc axiom RI   s f t = fprove fpc axiom (RF (f,idArr fpc (cod fpc f))) s f t

-- focus mode proofs of s ==f==> t where s and t are strictly alternating formulas
fprove :: Semigroup arr => FPCat ob arr -> (ob -> arr -> ob -> [ax]) -> FState arr -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr ax]
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
prove :: Semigroup arr => FPCat ob arr -> (ob -> arr -> ob -> [ax]) -> Frm ob arr -> arr -> Frm ob arr -> [Proof ob arr ax]
prove fpc axiom s f t = iprove fpc axiom BotI (altFrm s) f (altFrm t)
