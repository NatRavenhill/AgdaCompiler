module CompExp where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List 
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)

data instr : Set where
  Var  : String → instr
  Val  : ℕ → instr
  Add  : instr
  Not : instr
  Sub  : instr
  Joz  : ℕ → instr
  Err  : instr

program = List instr
stack   = List ℕ
state   = String → Maybe ℕ 


-- Not for natural numbers.
notN : ℕ -> ℕ
notN zero = suc zero
notN (suc n) = zero

⟨⟨_⟩⟩_,_,_ : program → stack → state → ℕ → Maybe stack 
⟨⟨ [] ⟩⟩ s , _ , _                         = just s
⟨⟨ _ ⟩⟩ s , _ , zero                       = just s
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k              = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k 
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k with σ x
...                            | just v  = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k
...                            | nothing = nothing
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k
⟨⟨ Not ∷ p ⟩⟩ (b ∷ s) , σ , suc k              = ⟨⟨ p ⟩⟩ (notN b ∷ s) , σ , k
⟨⟨ Joz n ∷ p ⟩⟩ (zero  ∷ s) , σ , suc k    = ⟨⟨ drop n p ⟩⟩ s , σ , k
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ s , σ , k
⟨⟨ _ ⟩⟩ _ , _ , _ = nothing 


data Exp : (A : Set) → Set where
  B   : 𝔹 → Exp 𝔹
  N   : ℕ → Exp ℕ
  V   : String → Exp ℕ 
  _⊕_ : Exp ℕ → Exp ℕ → Exp ℕ
-- 1. minus,
-- 2. and, or, not 

-- ≤ ≥ =

  if_then_else : Exp ℕ → Exp ℕ → Exp ℕ → Exp ℕ


-- 3. if then else, short-cut logical operators

-- 4. times, divide (short-cut?) ... we have no loops though! how would you extend the machine?
--           simple extension : more operations (boring)
--           complex extension : more control
infixl 5 _⊕_


⟦_⟧ : ∀ {T} → Exp T → state → Maybe ℕ
⟦ B( true ) ⟧ σ = just (suc zero)
⟦ B( false ) ⟧ σ = just zero
⟦ N(v) ⟧ σ = just v
⟦ V(s) ⟧ σ = σ s
⟦ E ⊕ E' ⟧ σ = ⟦ E ⟧ σ +' ⟦ E' ⟧ σ where
  _+'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m +' just n = just (m + n)
  _      +'      _ = nothing

⟦ if E then E′ else E″ ⟧ σ with ⟦ E ⟧ σ
...  | just zero    = ⟦ E″ ⟧ σ
...  | just (suc _) = ⟦ E′ ⟧ σ
...  | nothing      = nothing
--⟦ _ ⟧ _ = nothing

e0 : Exp ℕ
e0 =  N(1) ⊕ N(1) ⊕ V("x")

x0 : Maybe ℕ
x0 = ⟦ e0 ⟧ (λ v → nothing)

x1 : Maybe ℕ
x1 = ⟦ e0 ⟧ (λ v → just 1)

compile : ∀ {T} → Exp T → program
compile (N n)    = [ Val n ]
compile (V s)    = [ Var s ]
compile (E ⊕ E') = (compile E ++ compile E') ++ [ Add ]
compile (if E then E' else  E'') = e ++ [ Joz (length p') ] ++ p' ++ e ++ [ Not ] ++ [ Joz (length p'') ] ++ p''
    where
    e = compile E
    p' = compile E'
    p'' = compile E''
compile E        = [ Err ]

x2 : Maybe stack
x2 = ⟨⟨ compile e0 ⟩⟩ [] , (λ v → just 1) , 10

{-
Example
  << Val 1 ∷ Val 1 ∷ Add ∷ Var "x" ∷ Add ∷ [] >> [] --->
  << Val 1 ∷ Add ∷ Var "x" ∷ Add ∷ [] >> [1] -->
  << Add ∷ Var "x" ∷ Add ∷ [] >> [1::1] -->
  << Var "x" ∷ Add ∷ [] >> [2] -->
  << Add ∷ [] >> [1::2] -->
  << [] >> [3] -->
  just [3]
-}

--anything that has not been defined in compile will just be Err 
sound : (T : Set) (e : Exp T) (p : program) (n : ℕ)(σ : state) (k : ℕ) →
        ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ] → ⟦ e ⟧ σ ≡ just n 

--Booleans (Natalie)
sound .𝔹 (B x) p n σ zero () --can't have just [] ≡ just [ n ] so false
sound .𝔹 (B x) p n σ (suc k) () --can't have  nothing ≡ just [ n ]  so false  

--Constants (Natalie)
sound .ℕ (N x) p n σ zero ()  --can't have just [] ≡ just n so false
sound .ℕ (N zero) p zero σ (suc k) pf = refl
sound .ℕ (N zero) p (suc n) σ (suc k) ()
sound .ℕ (N (suc x)) p .(suc x) σ (suc k) refl = refl

--Variables (?)
sound .ℕ (V x) p n σ k  with σ x
sound .ℕ (V x) p n σ zero | just v  = {!!}
sound .ℕ (V x) p n σ (suc k) | just v  = {!!}
... | nothing  = {!!}

 -- where 
{-   lemma3 : ⟨⟨ [ Var x ] ⟩⟩ [] , σ , k ≡ just [ n ] → σ x ≡ just n
   lemma3 = {!!}-}

--Addition (?)
--⟨⟨ (compile e ++ compile e₁) ++ [ Add ] ⟩⟩ [] , σ , k ≡ just [ n ] →  (e _.+' e₁) σ (⟦ e ⟧ σ) (⟦ e₁ ⟧ σ) ≡ just n
sound .ℕ (e ⊕ e₁) p n σ k = {!!}

--Conditionals (?)
-- ⟨⟨ [ Err ] ⟩⟩ [] , σ , k ≡ just [ n ] →  (⟦ if e then e₁ else e₂ ⟧ σ | ⟦ e ⟧ σ) ≡ just n
sound .ℕ (if_then_else e e₁ e₂) p n σ k = {!!}
  
              
adeq : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ just n → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ])
adeq .𝔹 (B x) p σ n x₁ = {!!}
adeq .ℕ (N x) p σ n x₁ = {!!}
adeq .ℕ (V x) p σ n x₁ = {!!}
adeq .ℕ (e ⊕ e₁) p σ n x = {!!}
adeq .ℕ (if_then_else e e₁ e₂) p σ n x = {!!}
              
adeq-fail : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}

