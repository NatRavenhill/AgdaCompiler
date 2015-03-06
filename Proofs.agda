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

lemma2 : ∀ x σ k → (n m : ℕ) → σ x ≡ just m → ⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , k ≡ just (n ∷ []) → m ≡ n
lemma2 x σ zero n m p ()
lemma2 x σ (suc k) n m p q = {!!} 
  where
--  v : Maybe ℕ
--  v = ⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , suc k | p
lemma1 :  ∀ x σ k n → ⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , k ≡ just (n ∷ []) → σ x ≡ just n
lemma1 x σ k n with σ x | inspect σ x
... | just m | ⟪ eq ⟫ = {!!}
... | nothing | ⟪ eq ⟫ = {!!}

-------------------------
-- PROOF FOR SOUNDNESS --
-------------------------
--anything that has not been defined in compile will just be Err 
sound : (T : Set) (e : Exp T) (p : program) (n : ℕ)(σ : state) (k : ℕ) →
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

--soundness for Variables (Natalie)
--q proves that we can get n from compiling Var x
--show we can get v from compiling Var x
--then v must be equal to n
sound .ℕ (V x) p n σ k q  with σ x | inspect σ x 
sound .ℕ (V x) p n σ k q | just v | ⟪ eq ⟫ = {!eq!}
{-goal --v is equal to n, prove this! (Get just v from compile and get just n from [[V x]] σ) 
   where
   goal : just v ≡ just n
   goal = lemma1 x σ k n {!!}
-}
-- just v ≡[ {!!} ]  just n done
--   subgoal : ⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , k ≡ just v
 --  subgoal = ?

sound .ℕ (V x) p n σ k q | nothing | r = {!!}  --this should be false. q is a false statement

--soundness for addition (Natalie)
sound .ℕ (e ⊕ e₁) p n σ zero q = {!!}
sound .ℕ (e ⊕ e₁) p n σ (suc k) q = {!!}

sound .ℕ (e ⊝ e₁) p n σ k x = {!!}

sound .𝔹 (¬ e) p n σ k x = {!!}

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
adeq .𝔹 (B x) p σ n x₁ = {!!}
adeq .ℕ (N x) p σ n x₁ = {!!}
adeq .ℕ (V x) p σ n x₁ = {!!}
adeq .ℕ (e ⊕ e₁) p σ n x = {!!}
adeq .ℕ (if_then_else e e₁ e₂) p σ n x = {!!}

adeq _ _ _ _ _ _ = {!!} 
              
adeq-fail : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}
