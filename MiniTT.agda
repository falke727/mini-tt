module MiniTT where

-- Dependent producct --> Πp : A . B
-- Dependent sum      --> Σp : A . B
-- Labelled sum       --> Sum(c₁A₁ | ... | c_nA_n)

-- id : Π A : U . A → A = λA.λx.x
-- id : Π A : U . (Π _ : A . A) = λA.λx.x
id : (A : Set) → A → A
id = λ A → λ x → x

-- Bool : U = Sum (true | false)
data Bool : Set where
  true  : Bool
  false : Bool

-- elimBool : ΠC : Bool → U . C false → C true → Πb : Bool . C b
--          = λC.λh₀.λh₁.fun(true → h₁ | false → h₀)
-- elimBool : ΠC : (Bool → U) . (C false → (C true → Πb : Bool . C b))
--          = λC.λh₀.λh₁.fun(true → h₁ | false → h₀)
-- elimBool : ΠC : (Π _ : Bool . U) . (Π _ : C false . (Π _ : C true . (Πb : Bool . C b)))
--          = λC.λh₀.λh₁.fun(true → h₁ | false → h₀)

elimBool : (C : Bool → Set) → (C false) → (C true) → ((b : Bool) → C b)
elimBool C h₀ h₁ b with b
elimBool _ _  h₁ _ | true  = h₁
elimBool _ h₀ _  _ | false = h₀

-- rec Nat : U = Sum (zero | succ Nat)
data Nat : Set where
  zero : Nat
  succ : Nat → Nat

-- rec List : U → U = λA.Sum (nil | cons A × List A)
-- rec List : Π _ : U . U = λA.Sum (nil | cons A × List A)

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A
  

{--
   Πp : A . B is the type of functions taking an object M in type A to an object in
   the type B (where B may be dependend on M)

   Σp : A . B is the type of pairs M, N, where M ∈ A, N ∈ B[M/p].
   The projections are written M.1 ans M.2. It is possible to use the notation A × B
   as syntactic sugar for Σ_ : A . B
--}

-- rec natrec : ΠC : (Nat → U)  . (C zero)  → (Πn : Nat . C n → C (succ n)) → (Πn : Nat . C n)
--            = λC.λa.λg.fun(zero → a | succ n₁ → g n₁ (natrec C a g n₁))

natrec : (C : Nat → Set) → (C zero) → ((n : Nat) → C n → C (succ n)) → ((n : Nat) → C n)
natrec _ a _ zero      = a
natrec C a g (succ n₁) = g n₁ (natrec C a g n₁)

add : Nat → Nat → Nat
add x zero      = x
add x (succ y₁) = succ (add x y₁)
