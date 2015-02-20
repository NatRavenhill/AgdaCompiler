open import CompExp
open import IO
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.String renaming (_++_ to _^_; show to strshow)
open import Data.Nat.Show

testiffalse : Exp ℕ
testiffalse = (if (N( 0 )) then (N(1) ⊕ N(1)) else) (N ( 4 ))

testiftrue : Exp ℕ
testiftrue = (if (N( 1 )) then (N(1) ⊕ N(1)) else) (N ( 4 ))

iftrueval : Maybe stack
iftrueval = ⟨⟨ compile testiftrue ⟩⟩ [] , (λ x -> just zero) , 999

iffalseval : Maybe stack
iffalseval = ⟨⟨ compile testiffalse ⟩⟩ [] , (λ x -> just zero) , 999

getVal : Maybe stack -> Maybe ℕ
getVal nothing = nothing
getVal (just []) = nothing
getVal (just (n ∷ t)) = just n

open import Data.Unit

main = run (putN (getVal(iftrueval)))
    where
    putN : Maybe ℕ -> IO ⊤
    putN nothing = putStrLn ""
    putN (just n) = putStrLn (show n)
