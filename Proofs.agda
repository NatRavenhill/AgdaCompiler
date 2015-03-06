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

--soundness for booleans, proved by pattern matching (Natalie)
sound .ℕ (N zero) p n σ zero ()
sound .ℕ (N zero) p .0 σ (suc k) refl = refl
sound .ℕ (N (suc x)) p n σ zero ()
sound .ℕ (N (suc x)) p .(suc x) σ (suc k) refl = refl

--soundness for Variables (Natalie)
sound .ℕ (V x) p n σ k q  with σ x
sound .ℕ (V x) p n σ k q | just v = {!!} --v is equal to n, prove this! 
sound .ℕ (V x) p n σ k q | nothing = {!!}  --this should be false. q is a false statement

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
