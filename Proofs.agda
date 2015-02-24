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

-------------------------
-- PROOF FOR SOUNDNESS --
-------------------------
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
              
adeq-fail : (T : Set) (e : Exp T) (p : program) (σ : state) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}