---------------------------------------------------------------------------------
-- This module contains the compiler and stack-machine for AbstractSyntax.agda --
-- authors: Matthew Thompson, Natalie Ravenhill, Yu-Yang Lin                   --
---------------------------------------------------------------------------------
module CompExp where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List 
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)

-- module imports for the compiler.
open import AbstractSyntax

-- INSTRUCTION SET FOR STACK MACHINE.
data instr : Set where
  Var  : String → instr
  Val  : ℕ → instr
  Add  : instr
  Or   : instr
  Not  : instr
  Sub  : instr
  And  : instr
  Joz  : ℕ → instr
  Loop : ℕ → instr
  Err  : instr

-- DEFINITIONS FOR THE STACK MACHINE.
program = List instr
stack   = List ℕ
state   = String → Maybe ℕ 

-- Operation for natural numbers
notN : ℕ -> ℕ
notN zero = suc zero
notN (suc n) = zero

_andN_ : ℕ → ℕ → ℕ
zero andN _ = zero
suc(_) andN m = m

_orN_ : ℕ → ℕ → ℕ
_orN_ zero    n = n
_orN_ (suc n) _ = (suc n)

infixr 6 _andN_
infixr 5 _orN_

-- THIS IS THE STACK MACHINE, TRY NOT TO CHANGE IT.
⟨⟨_⟩⟩_,_,_ : program → stack → state → ℕ → Maybe stack 
⟨⟨ [] ⟩⟩ s , _ , _                         = just s
⟨⟨ _ ⟩⟩ s , _ , zero                       = just s
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k              = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k 
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k with σ x
...                            | just v  = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k
...                            | nothing = nothing
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k
⟨⟨ Not ∷ p ⟩⟩ (b ∷ s)     , σ , suc k      = ⟨⟨ p ⟩⟩ (notN b ∷ s) , σ , k
⟨⟨ And ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m andN n ∷ s) , σ , k 
⟨⟨ Or  ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ ((m orN n) ∷ s) , σ , k 
⟨⟨ Joz n ∷ p ⟩⟩ (zero  ∷ s) , σ , suc k    = ⟨⟨ drop n p ⟩⟩ s , σ , k
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ s , σ , k
⟨⟨ Loop n ∷ p ⟩⟩ (zero  ∷ s) , σ , suc k   = ⟨⟨ drop n p ⟩⟩ s , σ , k
⟨⟨ Loop n ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k   = ⟨⟨ (take n p) ++ Loop n ∷ p ⟩⟩ s , σ , k
⟨⟨ _ ⟩⟩ _ , _ , _ = nothing 

-- Compile takes an expression and returns a program (list of instructions).
compile : ∀ {T} → Exp T → program
compile (B true) = [ Val (suc zero) ]
compile (B false)= [ Val zero ]
compile (N n)    = [ Val n ]
compile (V s)    = [ Var s ]
compile (E ⊕ E') = (compile E ++ compile E') ++ [ Add ]
compile (E ⊝ E') = (compile E ++ compile E') ++ [ Sub ]
compile ( ¬ E )  = compile E ++ [ Not ]
compile (E & E') = compile E ++ compile E' ++ [ And ]
compile (E ∥ E') = compile E ++ compile E' ++ [ Or ]

compile (E <= E') = compile E' ++ [ Val (suc zero) ] ++ [ Add ] ++ compile E  ++ [ Sub ]
compile (E >= E') = compile E  ++ [ Val (suc zero) ] ++ [ Add ] ++ compile E' ++ [ Sub ]
compile (E == E') = sub1 ++ sub2 ++ [ And ]
    where
      e1 = compile E
      e2 = compile E'
      sub1 = e1 ++ [ Val (suc zero) ] ++ [ Add ] ++ e2  ++ [ Sub ]
      sub2 = e2 ++ [ Val (suc zero) ] ++ [ Add ] ++ e1  ++ [ Sub ]
-- DO NOT BUILD ON EXPRESSIONS, ONLY REDUCE TO MACHINE OPERATIONS.

compile (if E then E' else  E'') = e ++ [ Joz (length p') ] ++ p' ++ e ++ [ Not ] ++ [ Joz (length p'') ] ++ p''
    where
      e = compile E
      p' = compile E'
      p'' = compile E''

--compile (while E do E') = {!compile E' ++ while!} -- I CANT FIGURE THIS ONE OUT YET (YU-YANG)

compile (for E do E') = e ++ [ Loop (length p) ] ++ p
    where
      e  = compile E
      p  = compile E' ++ e ++ [ Val (suc zero) ] ++ [ Sub ]

compile (E ×× E') = e1 ++ [ Joz (length p') ] ++ p' ++ e1 ++ [ Not ] ++ [ Joz 1 ] ++ [ Val zero ]
    where
      e1 = compile E
      e2 = compile E'
      p  = e2 ++ e2 ++ [ Add ] ++ e1 ++ [ Val (suc zero) ] ++ [ Sub ]
      p' = [ Loop (length p) ] ++ p

--compile E = [ Err ]

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
