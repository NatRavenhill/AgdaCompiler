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
  FLoop : (List ℕ → 𝔹) → (ℕ → ℕ) → ℕ → instr
  Err  : instr

-- DEFINITIONS FOR THE STACK MACHINE.
program = List instr
stack   = List ℕ
state   = String → Maybe ℕ 

-- Operation for natural numbers
ℕto𝔹 : ℕ → ℕ
ℕto𝔹 zero  = zero
ℕto𝔹 (suc _) = suc zero

notN : ℕ -> ℕ
notN zero = suc zero
notN (suc n) = zero

_andN_ : ℕ → ℕ → ℕ
zero   andN _ = zero
suc(_) andN m = ℕto𝔹 m

_orN_ : ℕ → ℕ → ℕ
_orN_ zero    n = ℕto𝔹 n
_orN_ (suc n) _ = ℕto𝔹 (suc n)

_<'_ : ℕ → ℕ → 𝔹
_ <' zero = false
zero <' suc _ = true
suc a <' suc b = a <' b

_<=''_ : ℕ → ℕ → 𝔹
zero <='' _ = true
suc _ <='' zero = false
suc a <='' suc b = a <='' b

infixr 6 _andN_
infixr 5 _orN_

-- THIS IS THE STACK MACHINE, TRY NOT TO CHANGE IT.
⟨⟨_⟩⟩_,_,_ : program → stack → state → ℕ → Maybe stack 
⟨⟨ [] ⟩⟩ s , _ , _                       = just s
⟨⟨ _ ⟩⟩ s , _ , zero                     = just s
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k            = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k 
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k with σ x
...                            | just v  = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k
...                            | nothing = nothing
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k
⟨⟨ Not ∷ p ⟩⟩ (b ∷ s)     , σ , suc k    = ⟨⟨ p ⟩⟩ (notN b ∷ s) , σ , k
⟨⟨ And ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ (m andN n ∷ s) , σ , k 
⟨⟨ Or  ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ ((m orN n) ∷ s) , σ , k 
⟨⟨ Joz n ∷ p ⟩⟩ (zero  ∷ s) , σ , suc k  = ⟨⟨ drop n p ⟩⟩ s , σ , k
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k  = ⟨⟨ p ⟩⟩ s , σ , k

-- FLOOP takes the next n instructions and repeats them M times, where M = top of stack.
--  Drops them if stack top is zero.
--  Repeats them if stack top M is not zero. Then adds M-1 to top of stack.
⟨⟨ FLoop c f n ∷ p ⟩⟩ (v ∷ s) , σ , suc k with c (v ∷ s)
⟨⟨ FLoop c f n ∷ p ⟩⟩ v ∷ s , σ , suc k | true  = ⟨⟨ (take n p) ++ [ Val (f  v) ] ++ FLoop c f n ∷ p ⟩⟩ s , σ , k
⟨⟨ FLoop c f n ∷ p ⟩⟩ v ∷ s , σ , suc k | false = ⟨⟨ drop n p ⟩⟩ (v ∷ s) , σ , k 

⟨⟨ _ ⟩⟩ _ , _ , _ = nothing 

-- Compile takes an expression and returns a program (list of instructions).
compile : ∀ {T} → Exp T → program
compile (B true) = [ Val (suc zero) ]
compile (B false)= [ Val zero ]
compile (N n)    = [ Val n ]
compile (V s)    = [ Var s ]
compile (E ⊕ E') = (compile E ++ compile E') ++ [ Add ]
compile (E ⊝ E') = (compile E' ++ compile E) ++ [ Sub ]
compile ( ¬ E )  = compile E ++ [ Not ]
compile (E & E') = compile E ++ compile E' ++ [ And ]
compile (E ∥ E') = compile E ++ compile E' ++ [ Or ]

-- COMPARISON FUNCTIONS:
-- These use substraction to find which one is larger. 
-- The goal is to get a number greater than zero in the substraction.
-- If the number is indeed greater than zero, then the condition is true.
-- (And 1) instruction added at the end to convert the value to Booleans.
compile (E <= E') = compile E  ++ [ Val (suc zero) ] ++ compile E' ++ [ Add ] ++ [ Sub ] ++ [ Val (suc zero) ] ++ [ And ]
compile (E >= E') = compile E' ++ [ Val (suc zero) ] ++ compile E ++ [ Add ] ++ [ Sub ] ++ [ Val (suc zero) ] ++ [ And ]
compile (E == E') = sub1 ++ sub2 ++ [ And ]
    where
      e1 = compile E
      e2 = compile E'
      sub1 = e2 ++ e1 ++ [ Val (suc zero) ] ++ [ Add ] ++ [ Sub ]
      sub2 = e1 ++ e2 ++ [ Val (suc zero) ] ++ [ Add ] ++ [ Sub ]
-- DO NOT BUILD ON EXPRESSIONS, ONLY REDUCE TO MACHINE OPERATIONS.

compile (if E then E' else  E'') = e ++ [ Joz (length p') ] ++ p' ++ e ++ [ Not ] ++ [ Joz (length p'') ] ++ p''
    where
      e = compile E
      p' = compile E'
      p'' = compile E''

--compile (while E do E') = {!compile E' ++ while!} -- I CANT FIGURE THIS ONE OUT YET (YU-YANG)

--FOR LOOP:
--  compile E;
--  Loop to check on value of E.
--    if E is non-zero. Do E'.
--    if E is zero. Skip E'.
-- compile (for E do E') = e ++ [ FLoop (length p) ] ++ p
--     where
--       e  = compile E
--       p  = compile E'

-- MULTIPLICATION:
--  compile E;
--  Loop to check on value of E.
--    if E is non-zero. Do E'.
--    if E is zero. Skip E'.
--  Add e1 to stack.
--  NOT e1.
--  IF e1 == ZERO, then insert a ZERO in stack.
--  IF e1 != ZERO, then skip.
compile (E ×× E') = e1 ++ [ Joz (length p') ] ++ p' ++ 
                    e1 ++ [ Not ] ++ [ Joz 1 ] ++ [ Val zero ] ++ [ Joz 0 ]
    where
      e1 = [ Val (suc zero) ] ++ compile E ++ [ Sub ]
      e2 = compile E'
      p  = e2 ++ [ Add ]
      c : List ℕ → 𝔹
      c (x ∷ _) = 0 <' x
      c _         = false
      f  = λ n → n ∸ 1
      p' = e2 ++ e1 ++ [ FLoop c f (length p) ] ++ p

-- DIVISION
-- First check if E' is zero, then Err
-- Then check if E' > E then zero
-- Then loop from j = 0 until (j * b) <= a
-- The return (j - 1)
compile (E // E') = e2zero ++ [ Not ] ++ [ Joz (length div) ] ++ div ++ e2zero ++ [ Joz 1 ] ++ [ Err ] -- If e2 != zero then div else error
    where
      e1 = compile E
      e2 = compile E'
      e1less = e1 ++ e2 ++ [ Sub ] ++ [ Val (suc zero) ] ++ [ And ] -- e1 < e2
      c : List ℕ → 𝔹 -- Condition check
      c (j ∷ one ∷ a ∷ b ∷ s) = (j * b) <='' a
      c _                    = false
      f = λ n → n + 1 -- Increment
      p = e2 ++ e1 ++ [ Val 1 ] ++ [ Val 0 ] ++ [ FLoop c f 0 ] ++ [ Sub ] -- The loop
      div = e1less ++ [ Not ] ++ [ Joz (length p) ] ++ p ++ e1less ++ [ Joz 1 ] ++ [ Val zero ] -- If e1 < e2 then zero else div
      sub1 = e2 ++ [ Val zero ] ++ [ Val (suc zero) ] ++ [ Add ] ++ [ Sub ] -- Used for ==, to work out if e2 is zero
      sub2 = [ Val zero ] ++ e2 ++ [ Val (suc zero) ] ++ [ Add ] ++ [ Sub ]
      e2zero = sub1 ++ sub2 ++ [ And ] -- e2 == zero



compile E = [ Err ]



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
