module Permutation3 where

open import Data.Nat
open import Data.Vec
open import Data.Vec.Equality
open PropositionalEquality
  using ([]-cong; _∷-cong_)
  renaming (_≈_ to _≈ᵥ_; refl to reflᵥ; sym to symᵥ; trans to transᵥ)
open import Relation.Binary.Core
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (cong)
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

data Permutation {A : Set} : ∀ {n m} → Vec A n → Vec A m → Set where
  permEmpty : Permutation [] []
  permSkip  : ∀ {n m} {u : Vec A n} {v : Vec A m} {h}
              → Permutation u v
              → Permutation (h ∷ u) (h ∷ v)
  permSwap  : ∀ {n} {v : Vec A n} {h h′}
              → Permutation (h ∷ h′ ∷ v) (h′ ∷ h ∷ v)
  permTrans : ∀ {n m o} {a : Vec A n} {b : Vec A m} {c : Vec A o}
              → Permutation a b → Permutation b c → Permutation a c

eqPerm : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m} → u ≈ᵥ v → Permutation u v
eqPerm []-cong          = permEmpty
eqPerm (refl ∷-cong eq) = permSkip (eqPerm eq)

sym : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m} → Permutation u v → Permutation v u
sym permEmpty               = permEmpty
sym (permSkip perm)         = permSkip (sym perm)
sym permSwap                = permSwap
sym (permTrans perm₁ perm₂) = permTrans (sym perm₂) (sym perm₁)

perm-length-equal : ∀ {A : Set} {n m} {u : Vec A n} {v : Vec A m} → Permutation u v → n ≡ m
perm-length-equal permEmpty = refl
perm-length-equal (permSkip perm) = cong suc (perm-length-equal perm)
perm-length-equal permSwap = refl
perm-length-equal {n = n} {m = m} (permTrans {m = o} perm₁ perm₂) = begin
  n
    ≡⟨ perm-length-equal perm₁ ⟩
  o
    ≡⟨ perm-length-equal perm₂ ⟩
  m
    ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

isEquivalence : ∀ {A : Set} {n} → IsEquivalence (Permutation {A} {n})
isEquivalence = record
  { refl  = λ {xs} → eqPerm (reflᵥ xs)
  ; sym   = sym
  ; trans = permTrans
  }

Less : ∀ {n} → ℕ → Vec ℕ n → Set
Less _ []      = ⊤
Less a (x ∷ v) = a ≤ x × Less a v

Less-≤ : ∀ {x y n} {vs : Vec ℕ n} → x ≤ y → Less y vs → Less x vs
Less-≤ {vs = []}     _    _           = tt
Less-≤ {vs = v ∷ vs} x≤y (y≤v , y≤vs) = ≤-trans x≤y y≤v , Less-≤ x≤y y≤vs

Perm-≤ : ∀ {n m} {vs : Vec ℕ n} {us : Vec ℕ m} {a} → Less a vs → Permutation us vs → Less a us
Perm-≤ a≤vs               permEmpty               = tt
Perm-≤ (a≤v , a≤vs)       (permSkip perm)         = a≤v , Perm-≤ a≤vs perm
Perm-≤ (a≤x , a≤y , a≤vs) permSwap                = a≤y , a≤x , a≤vs
Perm-≤ a≤vs               (permTrans perm₁ perm₂) = Perm-≤ (Perm-≤ a≤vs perm₂) perm₁

Ordered : ∀ {n} → Vec ℕ n → Set
Ordered []      = ⊤
Ordered (x ∷ v) = Less x v × Ordered v

record Sorted-of {n} (vs : Vec ℕ n) : Set where
  field
    len     : ℕ
    vec     : Vec ℕ len
    ordered : Ordered vec
    perm    : Permutation vs vec
