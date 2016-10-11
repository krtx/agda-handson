module Permutation2 where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Vec
open import Relation.Binary.Core
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

open import Relation.Binary.PropositionalEquality using (trans)

-- data Permutation {A : Set} : ∀ {n} → Vec A n → Vec A n → Set where
--   permEmpty : Permutation [] []
--   permSkip  : ∀ {n} {u v : Vec A n} {h}
--               → Permutation u v
--               → Permutation (h ∷ u) (h ∷ v)
--   permSwap  : ∀ {n} {v : Vec A n} {h h′}
--               → Permutation (h ∷ h′ ∷ v) (h′ ∷ h ∷ v)
--   permTrans : ∀ {n} {a b c : Vec A n}
--               → Permutation a b → Permutation b c → Permutation a c

-- data Permutation {A : Set} : ∀ {n m} → n ≡ m → Vec A n → Vec A m → Set where
--   permEmpty : Permutation refl [] []
--   permSkip  : ∀ {n} {u v : Vec A n} {h}
--               → Permutation refl u v
--               → Permutation refl (h ∷ u) (h ∷ v)
--   permSwap  : ∀ {n} {v : Vec A n} {h h′}
--               → Permutation refl (h ∷ h′ ∷ v) (h′ ∷ h ∷ v)
--   permTrans : ∀ {n m o} {a : Vec A n} {b : Vec A m} {c : Vec A o}
--               → (n≡m : n ≡ m)
--               → (m≡o : m ≡ o)
--               → Permutation n≡m a b
--               → Permutation m≡o b c
--               → Permutation (trans n≡m m≡o) a c

data Permutation {A : Set} : ∀ {n m} → Vec A n → Vec A m → Set where
  permEmpty : Permutation [] []
  permSkip  : ∀ {n} {u v : Vec A n} {h}
              → Permutation u v
              → Permutation (h ∷ u) (h ∷ v)
  permSwap  : ∀ {n} {v : Vec A n} {h h′}
              → Permutation (h ∷ h′ ∷ v) (h′ ∷ h ∷ v)
  permTrans : ∀ {n m o} {a : Vec A n} {b : Vec A m} {c : Vec A o}
              → Permutation a b
              → Permutation b c
              → Permutation a c

permutation-length : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m} → Permutation u v → n ≡ m
permutation-length permEmpty = refl
permutation-length (permSkip perm) = refl
permutation-length permSwap = refl
permutation-length (permTrans perm₁ perm₂) = trans (permutation-length perm₁) (permutation-length perm₂)

-- permTrans-++-swap : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m}
--                     → Permutation (+-comm n m) (u ++ v) (v ++ u)
-- permTrans-++-swap {u = []} {[]} = permEmpty
-- permTrans-++-swap {u = []} {x ∷ v} = {!!}
-- permTrans-++-swap {u = x ∷ u} {[]} = {!!}
-- permTrans-++-swap {u = x ∷ u} {x₁ ∷ v} = {!!}

-- eqPerm : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m} → Permutation u v
-- eqPerm {u = []}    {[]}      eq   = permEmpty
-- eqPerm {u = x ∷ u} {.x ∷ .u} refl = permSkip (eqPerm {u = u} {v = u} refl)

-- eqPerm′ : ∀ {A : Set} {n} {u : Vec A n} → Permutation u u
-- eqPerm′ {u = []}    = permEmpty
-- eqPerm′ {u = x ∷ u} = permSkip (eqPerm′ {u = u})

sym : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m} → Permutation u v → Permutation v u
sym permEmpty               = permEmpty
sym (permSkip perm)         = permSkip (sym perm)
sym permSwap                = permSwap
sym (permTrans perm₁ perm₂) = permTrans (sym perm₂) (sym perm₁)

-- isEquivalence : ∀ {A : Set} {n} → IsEquivalence (Permutation {A} {n})
-- isEquivalence = record
--   { refl  = eqPerm refl
--   ; sym   = sym
--   ; trans = permTrans
--   }

-- Less : ∀ {n} → ℕ → Vec ℕ n → Set
-- Less _ []      = ⊤
-- Less a (x ∷ v) = a ≤ x × Less a v

-- Less-≤ : ∀ {x y n} {vs : Vec ℕ n} → x ≤ y → Less y vs → Less x vs
-- Less-≤ {vs = []}     _    _           = tt
-- Less-≤ {vs = v ∷ vs} x≤y (y≤v , y≤vs) = ≤-trans x≤y y≤v , Less-≤ x≤y y≤vs

-- Perm-≤ : ∀ {n} {vs us : Vec ℕ n} {a} → Less a vs → Permutation us vs → Less a us
-- Perm-≤ a≤vs               permEmpty               = tt
-- Perm-≤ (a≤v , a≤vs)       (permSkip perm)         = a≤v , Perm-≤ a≤vs perm
-- Perm-≤ (a≤x , a≤y , a≤vs) permSwap                = a≤y , a≤x , a≤vs
-- Perm-≤ a≤vs               (permTrans perm₁ perm₂) = Perm-≤ (Perm-≤ a≤vs perm₂) perm₁

-- Ordered : ∀ {n} → Vec ℕ n → Set
-- Ordered []      = ⊤
-- Ordered (x ∷ v) = Less x v × Ordered v

-- record Sorted-of {n} (vs : Vec ℕ n) : Set where
--   field
--     vec     : Vec ℕ n
--     ordered : Ordered vec
--     perm    : Permutation vec vs
