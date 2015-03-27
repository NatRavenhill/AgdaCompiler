----------------------------------------------------------------------
-- This module contains the proofs for the stack-machine's compiler --
-- authors: Matthew Thompson, Natalie Ravenhill, Yu-Yang Lin        --
----------------------------------------------------------------------
module Proofs where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List 
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)
open import Data.Empty

-- Stuff used for the proofs.
open import AbstractSyntax
open import DenSemantics
open import CompExp

----------------------------------------
---SYNTAX FOR EQUATIONAL REASONING---
-----------------------------------------
_≡[_]_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡[ refl ] refl = refl
infixr 2 _≡[_]_

_done : ∀ {A : Set} (x : A) → x ≡ x
x done = refl
infix 2 _done

--
cong-just-elim : {a b : List ℕ} → just a ≡ just b → a ≡ b
cong-just-elim p = cong f p
    where
      f : Maybe (List ℕ) → List ℕ 
      f (just x) = x
      f nothing = [] -- This case doesn't happen

--
cong-just-intro : {A : Set} {a b : A} → a ≡ b → just a ≡ just b
cong-just-intro p = cong f p
    where
      f : {B : Set} → B → Maybe B
      f x = just x

--
cong-list : {A : Set} {a b : A} → [ a ] ≡ [ b ] → a ≡ b
cong-list refl = refl


sym-trans : {A : Set} {a b c : A} → a ≡ b → a ≡ c → b ≡ c
sym-trans refl refl = refl

--⟨⟨ (compile e ++ compile e') ++ Add ∷ [] ⟩⟩ [] , σ , k ≡ ⟨⟨ Add ∷ [] ⟩⟩ (x2 ∷ x1 ∷ []) , σ , k
--⟨⟨ Add ∷ [] ⟩⟩ (x2 ∷ x1 ∷ []) , σ , k ≡ just [x1 + x2]

lemplus1 : ∀ σ k n e e' x1 x2 → ⟨⟨ (compile e ++ compile e') ++ [ Add ] ⟩⟩ [] , σ , k ≡ just [ n ]
                               → ⟦ e      ⟧ σ ≡ just x1
                               → ⟦ e'     ⟧ σ ≡ just x2 
                               → ⟦ e ⊕ e' ⟧ σ ≡ just n
lemplus1 σ k n e e' x1 x2 p q1 q2 with (⟦ e ⟧ σ) | (⟦ e' ⟧ σ)
lemplus1 σ k n e e' x1 x2 p refl refl | just .x1 | just .x2 = {!!}
lemplus1 σ k n e e' x1 x2 p q1 () | _ | nothing
lemplus1 σ k n e e' x1 x2 p () q2 | nothing | _


lemplus2 : ∀ σ k n e e' x1 x2 → ⟨⟨ compile e  ⟩⟩ [] , σ , k ≡ just [ x1 ]
                              → ⟨⟨ compile e' ⟩⟩ [] , σ , k ≡ just [ x2 ]
                              → ⟨⟨ (compile e ++ compile e') ++ [ Add ] ⟩⟩ [] , σ , k ≡ just [ n ]
                              → n ≡ (x1 + x2)
lemplus2 = {!!}

--from meeting
lemma :  (T : Set) (e : Exp T) (p : program) (n m : ℕ) (σ : state) (k , k' , k'' : ℕ) (s , s' : stack) → 
               ⟨⟨ compile e ++ p ⟩⟩ s , σ , k ≡ ⟨⟨ p ⟩⟩ (m ∷ s) , σ , k' → 
               ⟨⟨ p ⟩⟩ (n ∷ s) , σ , k'' ≡ just s' →
               ⟦ e ⟧ σ ≡ just n
lemma  = {!!}


----from meeting
lemma2 :  {T : Set} (e e' : Exp T) (i : instr) (p : program) (m n : ℕ) (σ : state) (k k' : ℕ) (s : stack) → 
               ⟨⟨ compile e ⟩⟩ s , σ , k ≡ just [ n ] → 
               compile e ≡ compile e' ++ [ i ] →
               ⟨⟨ compile e' ++ [ i ] ⟩⟩ s , σ , k ≡ ⟨⟨ [ i ] ⟩⟩ (m ∷ s) , σ , k' →
               ⟦ e'  ⟧ σ ≡ just m
lemma2 = λ e e' i p m n σ k k' s x x₁ x₂ → {!!}

-------------------------
-- PROOF FOR SOUNDNESS --
-------------------------
--anything that has not been defined in compile will just be Err 
--if k is zero at start will always return just []
sound : (T : Set) (e : Exp T) (p : program) (n : ℕ) (σ : state) (k : ℕ) →
        ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ] → ⟦ e ⟧ σ ≡ just n 

--soundness for booleans, proved by pattern matching (Natalie)
sound .𝔹 (B true) p n σ zero ()
sound .𝔹 (B false) p n σ zero ()
sound .𝔹 (B true) p .1 σ (suc k) refl = refl
sound .𝔹 (B false) p .0 σ (suc k) refl = refl

--soundness for nats, proved by pattern matching (Natalie)
sound .ℕ (N zero) p n σ zero ()
sound .ℕ (N zero) p .0 σ (suc k) refl = refl
sound .ℕ (N (suc x)) p n σ zero ()
sound .ℕ (N (suc x)) p .(suc x) σ (suc k) refl = refl

--soundness for Variables (Natalie & Mat & Yu)
--q proves that we can get n from compiling Var x
--show we can get v from compiling Var x
--then v must be equal to n
sound .ℕ (V x) p n σ k q  with inspect σ x 
sound .ℕ (V x) p n σ zero () | ⟪ eq ⟫
sound .ℕ (V x) p n σ (suc k) q | ⟪ eq ⟫ = varlemma1 x σ k n q where

  varlemma1 :  ∀ x σ k n → ⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , (suc k) ≡ just [ n ] → σ x ≡ just n
  varlemma1 x σ k n p with σ x
  ... | just m = cong-just-intro (cong-list (cong-just-elim p))
  varlemma1 x σ k n () | nothing

--soundness for addition (Natalie)
sound .ℕ (e1 ⊕ e2) p n σ k q ={!!}
   where
     soundAdd :  (e1 , e2 : Exp ℕ) (p : program) (n : ℕ) (σ : state) (k : ℕ) →
        ⟨⟨ compile (e1 ⊕ e2) ⟩⟩ [] , σ , k ≡ just [ n ] →
        ⟦ e1 ⊕ e2 ⟧ σ ≡ just n         
     soundAdd e1 e2 _ p n σ k x = {!lemma!}
      where
        IH₁ : (x1 : ℕ) → ⟨⟨ compile e1 ⟩⟩ [] , σ , k ≡ just [ x1 ] → ⟦ e1 ⟧ σ ≡ just x1
        IH₁ x1 = sound ℕ e1 p x1 σ k
        IH₂ : (x2 : ℕ ) → ⟨⟨ compile e2 ⟩⟩ [] , σ , k ≡ just [ x2 ] → ⟦ e2 ⟧ σ ≡ just x2
        IH₂ x2 = sound ℕ e2 p x2 σ k        
        lemma1 : (p : program) (s , s' : stack) (k' , k'' : ℕ) (x1 , m : ℕ) → ⟨⟨ compile e1 ++ p ⟩⟩ s , σ , k ≡ ⟨⟨ p ⟩⟩ x1 ∷ s , σ , k'  → 
                         ⟦ e1 ⟧ σ ≡ just x1
        lemma1 p s k' x3 = {!!} 
{-
sound .ℕ (e1 ⊕ e2) p n σ k q with (⟦ e1 ⟧ σ) | (⟦ e2 ⟧ σ) | inspect ⟦ e1 ⟧ σ | inspect ⟦ e2 ⟧ σ 
sound .ℕ (e1 ⊕ e2) p zero σ k q | just zero | just zero | ⟪ eq1 ⟫ | ⟪ eq2 ⟫ = refl
sound .ℕ (e1 ⊕ e2) p n σ k q | just x1 | just x2 | ⟪ eq1 ⟫ | ⟪ eq2 ⟫ = {!!}
sound .ℕ (e1 ⊕ e2) p n σ k q | just x | nothing | ⟪ eq1 ⟫ | ⟪ eq2 ⟫  = {!!}
sound .ℕ (e1 ⊕ e2) p n σ k q | nothing | just x | ⟪ eq1 ⟫ | ⟪ eq2 ⟫  = {!!}
sound .ℕ (e1 ⊕ e2) p n σ k q | nothing | nothing | ⟪ eq1 ⟫ | ⟪ eq2 ⟫ = {!!} where
-}
 {-lemplus : ∀ σ k n e1 e2 x1 x2 → ⟨⟨ (compile e1 ++ compile e2) ++ Add ∷ [] ⟩⟩ [] , σ , (suc k) ≡ just [ n ]
                    → ⟦ e1 ⟧ σ ≡ just x1 → ⟦ e2 ⟧ σ ≡ just x2 
                    → ⟦ e1 ⊕ e2 ⟧ σ ≡ just (x1 + x2)
      lemplus σ k n e1 e2 x1 x2 = {!!}-}




-- Soundness for subtraction
sound .ℕ (e ⊝ e₁) p n σ zero q = {!!}
sound .ℕ (e ⊝ e₁) p n σ (suc k) x = {!!}

--match on each case of ⟦ e ⟧ σ
sound .𝔹 (¬ e) p  n σ k x with compile e | ⟦ e ⟧ σ
sound .𝔹 (¬ e) p n σ zero () | [] | d
sound .𝔹 (¬ e) p n σ (suc k) () | [] | d
sound .𝔹 (¬ e) p n σ zero () | a ∷ as | d
sound .𝔹 (¬ e) p n σ (suc k) x | a ∷ as | d with ⟨⟨ a ∷ as ++ Not ∷ [] ⟩⟩ [] , σ , (suc k) 
sound .𝔹 (¬ e) p n σ (suc k) () | a ∷ as | d | just []
sound .𝔹 (¬ e) p 1 σ (suc k) x | a ∷ as | just zero | just m = refl
sound .𝔹 (¬ e) p n σ (suc k) x | a ∷ as | just zero | just (suc zero ∷ []) = cong-just-intro (sym (cong-list (sym (cong-just-elim x))))
sound .𝔹 (¬ e) p n σ (suc k) x | a ∷ as | just zero | just (b ∷ bs) = {!!}
sound .𝔹 (¬ e) p n σ (suc k) x | a ∷ as | just (suc m) | just (b ∷ bs) = {!!}
sound .𝔹 (¬ e) p n σ (suc k) x | a ∷ as | nothing | just (b ∷ bs) = {!!}
sound .𝔹 (¬ e) p n σ (suc k) () | a ∷ as | d | nothing

sound .𝔹 (e & e₁) p n σ k x = {!!}

sound .𝔹 (e ∥ e₁) p n σ k x = {!!}

sound .𝔹 (e <= e₁) p n σ k x = {!!}

sound .𝔹 (e >= e₁) p n σ k x = {!!}

sound .𝔹 (e AbstractSyntax.== e₁) p n σ k x = {!!}

sound .ℕ (if_then_else e e₁ e₂) p n σ k x = {!!}

sound .ℕ (e ⊗ e₁) p n σ k x = {!!}

sound .ℕ (e ⊘ e₁) p n σ k x = {!!}

sound .ℕ (for e do e₁) p n σ k x = {!!}
  
------------------------
-- PROOF FOR ADEQUACY --
------------------------
adeq : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ just n → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ])
adeq .𝔹 (B true) p σ zero ()
adeq .𝔹 (B true) p σ (suc zero) refl = suc zero , refl 
adeq .𝔹 (B true) p σ (suc n) x =  {!!} --get this in one step, other steps are redundant?
adeq .𝔹 (B false) p σ zero x = {!!}
adeq .𝔹 (B false) p σ (suc n) ()

adeq .ℕ (N m) p σ n x = {!!}
adeq .ℕ (V v) p σ n x = {!!}
adeq .ℕ (e ⊕ e₁) p σ n x = {!!}
adeq .ℕ (e ⊝ e₁) p σ n x = {!!}

adeq .𝔹 (¬ e) p σ n x with compile e | ⟦ e ⟧ σ
adeq .𝔹 (¬ e) p σ n x | l | just zero = {!!}
adeq .𝔹 (¬ e) p σ n x | l | just (suc _) = {!!}
adeq .𝔹 (¬ e) p σ n () | l | nothing

adeq .𝔹 (e & e₁) p σ n x = {!!}
adeq .𝔹 (e ∥ e₁) p σ n x = {!!}
adeq .𝔹 (e <= e₁) p σ n x = {!!}
adeq .𝔹 (e >= e₁) p σ n x = {!!}
adeq .𝔹 (e AbstractSyntax.== e₁) p σ n x = {!!}
adeq .ℕ (if_then_else e e₁ e₂) p σ n x = {!!}
adeq .ℕ (e ⊗ e₁) p σ n x = {!!}
adeq .ℕ (e ⊘ e₁) p σ n x = {!!}
adeq .ℕ (for e do e₁) p σ n x = {!!}
              
adeq-fail : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}
