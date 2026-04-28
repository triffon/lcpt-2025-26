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

data H = Base Λ | Fun { fun :: H -> H }

type Valuation = String -> H

modify :: Valuation -> String -> H -> Valuation
modify ξ x a y
 | x == y    = a
 | otherwise = ξ y

evaluate :: Λ -> Valuation -> H
evaluate (Var x)    ξ = ξ x
{-
evaluate (m₁ :@ m₂) ξ =  f $ evaluate m₂ ξ
  where Fun f = evaluate m₁ ξ
-}
evaluate (m₁ :@ m₂) ξ =  fun (evaluate m₁ ξ) $ evaluate m₂ ξ
evaluate (L x n)    ξ = Fun (\a -> evaluate n $ modify ξ x a)

(⇑) :: Λ -> T -> H
m ⇑ (TVar _)  = Base m
m ⇑ (ρ :=> σ) = Fun (\a -> m :@ (a ⇓ ρ) ⇑ σ)  

(⇓) :: H -> T -> Λ
(Base m) ⇓ (TVar _)  = m
(Fun f)  ⇓ (ρ :=> σ) = L "x" ((f (Var "x" ⇑ ρ)) ⇓ σ)

nbe :: Λ -> T -> Λ
nbe m τ = (evaluate m error) ⇓ τ

ii = nbe (i :@ i) tid
kii = nbe (k :@ i :@ i) tid
c8 = nbe (cplus :@ c 3 :@ c 5) tn
