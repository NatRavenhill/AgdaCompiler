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
open import Data.String renaming (_++_ to _^_; _==_ to _≡≡_)

data Exp : (A : Set) → Set where
-- variables and data types
  B   : 𝔹 → Exp 𝔹
  N   : ℕ → Exp ℕ
  V   : String → Exp ℕ 

-- arithmetic operators
  _⊕_ : Exp ℕ → Exp ℕ → Exp ℕ
  _⊝_ : Exp ℕ → Exp ℕ → Exp ℕ 

-- boolean operators
  ¬   : Exp 𝔹 → Exp 𝔹
  _&_ : Exp 𝔹 → Exp 𝔹 → Exp 𝔹
  _∥_ : Exp 𝔹 → Exp 𝔹 → Exp 𝔹
  _<=_ : Exp ℕ → Exp ℕ → Exp 𝔹
  _>=_ : Exp ℕ → Exp ℕ → Exp 𝔹
  _==_ : Exp ℕ → Exp ℕ → Exp 𝔹

-- 3. if then else, short-cut logical operators
  if_then_else : Exp ℕ → Exp ℕ → Exp ℕ → Exp ℕ -- added by Matthew

-- 4. times, divide (short-cut?) ... we have no loops though! how would you extend the machine?
  _××_    : Exp ℕ → Exp ℕ → Exp ℕ
  _//_       : Exp ℕ → Exp ℕ → Exp ℕ

--  while_do_ : Exp 𝔹 → Exp ℕ → Exp ℕ --not sure if we will need this.
  for_do_ : Exp ℕ → Exp ℕ → Exp ℕ
--           simple extension : more operations (boring)
--           complex extension : more control
-- maybe define while-loop
infixr 5 _⊕_
infixr 5 _⊝_
infixr 6 _&_
infixr 5 _∥_
infixr 4 _<=_
infixr 4 _>=_
infixr 4 _==_
