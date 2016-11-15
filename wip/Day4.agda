module Day3 where

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

-- 実は data Permutation′ {A : Set} : ∀ {n m} → Vec A n → Vec A m → Set where という型のほうが良い

Less : ∀ {n} → ℕ → Vec ℕ n → Set
Less _ []      = ⊤
Less a (x ∷ v) = a ≤ x × Less a v

Ordered : ∀ {n} → Vec ℕ n → Set
Ordered []      = ⊤
Ordered (x ∷ v) = Less x v × Ordered v

record Sorted-of {n} (vs : Vec ℕ n) : Set where
  field
    vec     : Vec ℕ n
    ordered : Ordered vec
    perm    : Permutation vec vs

insert : ∀ {n} (a : ℕ) (vs : Vec ℕ n)
         → Ordered vs
         → Sorted-of (a ∷ vs)
insert = {!!}

insert-sort : ∀ {n} (vs : Vec ℕ n) → Sorted-of vs
insert-sort = {!!}

