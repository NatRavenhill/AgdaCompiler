--------------------------------------------------------------------
-- This module contains the Denotational Semantics for AbstractSyntax.agda --
-- authors: Matthew Thompson, Natalie Ravenhill, Yu-Yang Lin      --
--------------------------------------------------------------------
module DenSemantics where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List 
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)

-- module imports for the Expressions.
open import AbstractSyntax
open import CompExp

⟦_⟧ : ∀ {T} → Exp T → state → Maybe ℕ
⟦ B( true ) ⟧ σ = just (suc zero)
⟦ B( false ) ⟧ σ = just zero
⟦ N(v) ⟧ σ = just v
⟦ V(s) ⟧ σ = σ s

⟦ E ⊕ E' ⟧ σ = ⟦ E ⟧ σ +' ⟦ E' ⟧ σ where
  _+'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m +' just n = just (m + n)
  _      +' _      = nothing

⟦ E ⊝ E' ⟧ σ = ⟦ E ⟧ σ -' ⟦ E' ⟧ σ where
 _-'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ 
 just m -' just n = just (m ∸ n)
 _      -' _      = nothing

⟦ ¬( E ) ⟧ σ with ⟦ E ⟧ σ
... | just zero = just (suc zero)
... | just (suc _) = just zero
... | nothing = nothing

⟦ E & E' ⟧ σ = ⟦ E ⟧ σ &' ⟦ E' ⟧ σ where
  _&'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m &' just n = just (m andN n)
  _      &' _      = nothing

⟦ E ∥ E' ⟧ σ = ⟦ E ⟧ σ ∥' ⟦ E' ⟧ σ where
  _∥'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m ∥' just n = just (m orN n)
  _      ∥' _      = nothing

⟦ E <= E' ⟧ σ = ⟦ E ⟧ σ <=' ⟦ E' ⟧ σ where
  _<='_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m <=' just n = just ((suc n) ∸ m)
  _      <=' _      = nothing

⟦ E >= E' ⟧ σ = ⟦ E ⟧ σ >=' ⟦ E' ⟧ σ where
  _>='_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m >=' just n = just ((suc m) ∸ n)
  _      >=' _      = nothing

⟦ E == E' ⟧ σ = ⟦ E ⟧ σ ==' ⟦ E' ⟧ σ where
  _=='_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m ==' just n = just (((suc m) ∸ n) andN ((suc n) ∸ m))
  _      ==' _      = nothing

⟦ if E then E′ else E″ ⟧ σ with ⟦ E ⟧ σ
...  | just zero    = ⟦ E″ ⟧ σ
...  | just (suc _) = ⟦ E′ ⟧ σ
...  | nothing      = nothing

⟦ _ ⟧ _ = nothing

e0 : Exp ℕ
e0 =  N(1) ⊕ N(1) ⊕ V("x")

x0 : Maybe ℕ
x0 = ⟦ e0 ⟧ (λ v → nothing)

x1 : Maybe ℕ
x1 = ⟦ e0 ⟧ (λ v → just 1)

x2 : Maybe stack
x2 = ⟨⟨ compile e0 ⟩⟩ [] , (λ v → just 1) , 10

if1 : Maybe stack
if1 = ⟨⟨ compile ((if N(0) then N(4) else) (N(3)) ) ⟩⟩ [] , (λ x -> just 0) , 999

subt : Maybe stack
subt = ⟨⟨ compile ((N 28) ⊝ (N 6)) ⟩⟩ [] , (λ x -> just 0) , 999

timest : Maybe stack
timest = ⟨⟨ compile ((N 28) ×× (N 62)) ⟩⟩ [] , (λ x -> just 0) , 999

-- TO TEST: (YU-YANG)
-- gte, lte, eq, for.
