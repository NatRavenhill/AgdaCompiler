--------------------------------------------------------------------
-- This module contains the Abstract Syntax for the stack-machine --
-- authors: Matthew Thompson, Natalie Ravenhill, Yu-Yang Lin      --
--------------------------------------------------------------------
module AbstractSyntax where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List 
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)

data Exp : (A : Set) → Set where
  B   : 𝔹 → Exp 𝔹
  N   : ℕ → Exp ℕ
  V   : String → Exp ℕ 
  _⊕_ : Exp ℕ → Exp ℕ → Exp ℕ
-- 1. minus,
-- 2. and, or, not 
  ¬   : Exp ℕ -> Exp ℕ
  _&_   : Exp ℕ -> Exp ℕ -> Exp ℕ
-- ≤ ≥ =

  if_then_else : Exp ℕ → Exp ℕ → Exp ℕ → Exp ℕ -- added by Matthew


-- 3. if then else, short-cut logical operators

-- 4. times, divide (short-cut?) ... we have no loops though! how would you extend the machine?
--           simple extension : more operations (boring)
--           complex extension : more control
infixl 5 _⊕_
