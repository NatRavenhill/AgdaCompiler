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
  Sub  : instr
  Joz  : ℕ → instr
  Err  : instr

program = List instr
stack   = List ℕ
state   = String → Maybe ℕ 

⟨⟨_⟩⟩_,_,_ : program → stack → state → ℕ → Maybe stack 
⟨⟨ [] ⟩⟩ s , _ , _                         = just s
⟨⟨ _ ⟩⟩ s , _ , zero                       = just s
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k              = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k 
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k with σ x
...                            | just v  = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k 
...                            | nothing = nothing
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k
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
  if_then_else : Exp 𝔹 → Exp ℕ → Exp ℕ → Exp ℕ
-- 3. if then else, short-cut logical operators
-- 4. times, divide (short-cut?) ... we have no loops though! how would you extend the machine?
--           simple extension : more operations (boring)
--           complex extension : more control
infixl 5 _⊕_


⟦_⟧ : ∀ {T} → Exp T → state → Maybe ℕ
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
⟦ _ ⟧ _ = nothing

e0 =  N(1) ⊕ N(1) ⊕ V("x")
x0 = ⟦ e0 ⟧ (λ v → nothing)
x1 = ⟦ e0 ⟧ (λ v → just 1)

compile : ∀ {T} → Exp T → program
compile (N n)    = [ Val n ]
compile (V s)    = [ Var s ]
compile (E ⊕ E') = (compile E ++ compile E') ++ [ Add ]
compile E        = [ Err ]

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

sound : (T : Set) (e : Exp T) (p : program) (n : ℕ)(σ : state) (k : ℕ) →
        ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ] → ⟦ e ⟧ σ ≡ just n 
sound = {!!}
              
adeq : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ just n → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ])
adeq = {!!}
              
adeq-fail : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}
              
