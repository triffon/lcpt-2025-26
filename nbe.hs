import Data.Unique

data T = TVar String | T :=> T
  deriving (Eq, Ord, Show, Read)

α = TVar "α"
β = TVar "β"

tid = α :=> α
tk = α :=> (β :=> α)
tn = tid :=> tid

data Λ = Var String | Λ :@ Λ | L String Λ
  deriving (Eq, Ord, Show, Read)

x = Var "x"
y = Var "y"
z = Var "z"
f = Var "f"
m = Var "m"
n = Var "n"

i = L "x" x
k = L "x" $ L "y" x
c n = L "f" $ L "x" $ iterate (f :@) x !! n
cplus = L "m" $ L "n" $ L "f" $ L "x"
           (m :@ f :@ (n :@ f :@ x))
cmult = L "m" $ L "n" $ L "f" (m :@ (n :@ f))

data H = Base Λ | Fun { fun :: H -> IO H }

type Valuation = String -> IO H

modify :: Valuation -> String -> H -> Valuation
modify ξ x a y
 | x == y    = return a
 | otherwise = ξ y

evaluate :: Λ -> Valuation -> IO H
evaluate (Var x)    ξ = ξ x
{-
evaluate (m₁ :@ m₂) ξ =  f $ evaluate m₂ ξ
  where Fun f = evaluate m₁ ξ
-}
evaluate (m₁ :@ m₂) ξ =  do
  f <- evaluate m₁ ξ
  a <- evaluate m₂ ξ
  fun f a
evaluate (L x n)    ξ = return $ Fun (\a -> evaluate n $ modify ξ x a)

(⇑) :: Λ -> T -> IO H
m ⇑ (TVar _)  = return $ Base m
m ⇑ (ρ :=> σ) = return $ Fun (\a -> do
                                 aρ <- a ⇓ ρ
                                 m :@ aρ ⇑ σ)

(⇓) :: H -> T -> IO Λ
(Base m) ⇓ (TVar _)  = return m
(Fun f)  ⇓ (ρ :=> σ) = do
  x <- genSym
  xρ <- Var x ⇑ ρ
  a <- f xρ
  aσ <- a ⇓ σ
  return $ L x aσ

genSym :: IO String
{-
genSym = do
  n <- hashUnique <$> newUnique
  return $ "x" ++ show n
-}
genSym = (("x" ++) . show . hashUnique) <$> newUnique

type Context = String -> T

nbe :: Context -> Λ -> T -> IO Λ
nbe γ m τ = evaluate m (\x -> Var x ⇑ γ x) >>= (⇓ τ)

empty = error
γ "f" = tid
γ "x" = α
γ _   = error "Invalid variable"

ii = nbe empty (i :@ i) tid
kii = nbe empty (k :@ i :@ i) tid
c8 = nbe empty (cplus :@ c 3 :@ c 5) tn
f8x = nbe γ (cplus :@ c 3 :@ c 5 :@ f :@ x) α
cM = nbe empty (cmult :@ c 1000 :@ c 1000) tn
test = (/= x) <$> cM
