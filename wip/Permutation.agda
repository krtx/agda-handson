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

-- data Permutation′ {A : Set} : ∀ {n m} → Vec A n → Vec A m → Set where

eqPerm : ∀ {A : Set} {n} {u v : Vec A n} → u ≡ v → Permutation u v
eqPerm {u = []}    {[]}      eq   = permEmpty
eqPerm {u = x ∷ u} {.x ∷ .u} refl = permSkip (eqPerm {u = u} {v = u} refl)

eqPerm′ : ∀ {A : Set} {n} {u : Vec A n} → Permutation u u
eqPerm′ {u = []}    = permEmpty
eqPerm′ {u = x ∷ u} = permSkip (eqPerm′ {u = u})

sym : ∀ {A : Set} {n} {u v : Vec A n} → Permutation u v → Permutation v u
sym permEmpty               = permEmpty
sym (permSkip perm)         = permSkip (sym perm)
sym permSwap                = permSwap
sym (permTrans perm₁ perm₂) = permTrans (sym perm₂) (sym perm₁)

isEquivalence : ∀ {A : Set} {n} → IsEquivalence (Permutation {A} {n})
isEquivalence = record
  { refl  = eqPerm refl
  ; sym   = sym
  ; trans = permTrans
  }

Less : ∀ {n} → ℕ → Vec ℕ n → Set
Less _ []      = ⊤
Less a (x ∷ v) = a ≤ x × Less a v

Less-≤ : ∀ {x y n} {vs : Vec ℕ n} → x ≤ y → Less y vs → Less x vs
Less-≤ {vs = []}     _    _           = tt
Less-≤ {vs = v ∷ vs} x≤y (y≤v , y≤vs) = ≤-trans x≤y y≤v , Less-≤ x≤y y≤vs

Perm-≤ : ∀ {n} {vs us : Vec ℕ n} {a} → Less a vs → Permutation us vs → Less a us
Perm-≤ a≤vs               permEmpty               = tt
Perm-≤ (a≤v , a≤vs)       (permSkip perm)         = a≤v , Perm-≤ a≤vs perm
Perm-≤ (a≤x , a≤y , a≤vs) permSwap                = a≤y , a≤x , a≤vs
Perm-≤ a≤vs               (permTrans perm₁ perm₂) = Perm-≤ (Perm-≤ a≤vs perm₂) perm₁

Ordered : ∀ {n} → Vec ℕ n → Set
Ordered []      = ⊤
Ordered (x ∷ v) = Less x v × Ordered v

record Sorted-of {n} (vs : Vec ℕ n) : Set where
  field
    vec     : Vec ℕ n
    ordered : Ordered vec
    perm    : Permutation vec vs
