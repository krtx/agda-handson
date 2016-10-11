module Permutation where

open import Data.Nat
open import Data.Vec
open import Relation.Binary.Core
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

data Permutation {A : Set} : ∀ {n} → Vec A n → Vec A n → Set where
  permEmpty : Permutation [] []
  permSkip  : ∀ {n} {u v : Vec A n} {h}
              → Permutation u v
              → Permutation (h ∷ u) (h ∷ v)
  permSwap  : ∀ {n} {v : Vec A n} {h h′}
              → Permutation (h ∷ h′ ∷ v) (h′ ∷ h ∷ v)
  permTrans : ∀ {n} {a b c : Vec A n}
              → Permutation a b → Permutation b c → Permutation a c
