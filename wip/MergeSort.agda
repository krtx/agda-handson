module MergeSort where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
import Data.Fin as F
open import Data.Vec as V using (Vec; _++_; _∷_)
import Data.Vec.Equality
open Data.Vec.Equality.PropositionalEquality
  using ([]-cong; _∷-cong_)
  renaming (_≈_ to _≈ᵥ_; refl to reflᵥ; sym to symᵥ; trans to transᵥ)
open import Permutation3
open import Relation.Binary.PropositionalEquality

open import Data.Vec.Properties

infix 4 _⊝_

data SVec (A : Set) : ℕ → Set where
  []  : SVec A zero
  [_] : (x : A) → SVec A 1
  _⊝_ : ∀ {n m} (vl : SVec A n) (vr : SVec A m) → SVec A (n + m)

flatten : ∀ {A} {n} → SVec A n → Vec A n
flatten []        = V.[]
flatten [ x ]     = V.[ x ]
flatten (vl ⊝ vr) = flatten vl ++ flatten vr

data Splitted {A : Set} : ∀ {n m} → SVec A n → Vec A m → Set where
  nil : Splitted [] Vec.[]
  singleton : ∀ {x} → Splitted [ x ] (x ∷ Vec.[])
  split : ∀ {n m o p} {vs : SVec A n} {us : SVec A m} {vs′ : Vec A o} {us′ : Vec A p}
          → Splitted vs vs′
          → Splitted us us′
          → Splitted (vs ⊝ us) (vs′ ++ us′)

ordered-++-[] : ∀ {n} {vs : Vec ℕ n} → Ordered vs → Ordered (vs ++ Vec.[])
ordered-++-[] {vs = Vec.[]} ordered = tt
ordered-++-[] {vs = x ∷ vs} (le , ordered) = less-++-[] le , (ordered-++-[] ordered)
  where
    less-++-[] : ∀ {n} {x} {vs : Vec ℕ n} → Less x vs → Less x (vs ++ Vec.[])
    less-++-[] {vs = Vec.[]}         le         = tt
    less-++-[] {x = x} {vs = y ∷ vs} (x≤y , le) = x≤y , less-++-[] le

perm-++-[] : ∀ {n m} {vs : Vec ℕ n} {us : Vec ℕ m} → Permutation vs us → Permutation (vs ++ Vec.[]) (us ++ Vec.[])
perm-++-[] permEmpty = permEmpty
perm-++-[] (permSkip perm) = permSkip (perm-++-[] perm)
perm-++-[] permSwap = permSwap
perm-++-[] (permTrans perm₁ perm₂) = permTrans (perm-++-[] perm₁) (perm-++-[] perm₂)

sorted-of-++-[] : ∀ {n} {vs : Vec ℕ n} → Sorted-of vs → Sorted-of (vs ++ Vec.[])
sorted-of-++-[] sorted = record { len     = Sorted-of.len sorted + zero
                                ; vec     = Sorted-of.vec sorted ++ Vec.[]
                                ; ordered = ordered-++-[] (Sorted-of.ordered sorted)
                                ; perm    = perm-++-[] (Sorted-of.perm sorted)
                                }

merge : ∀ {n m} (vs₀ : Vec ℕ n) (vs₁ : Vec ℕ m)
        → Sorted-of vs₀
        → Sorted-of vs₁
        → Sorted-of (vs₀ ++ vs₁)
merge Vec.[] vs₁ sorted-vs₀ sorted-vs₁ = sorted-vs₁
merge vs₀ Vec.[] sorted-vs₀ sorted-vs₁ = sorted-of-++-[] sorted-vs₀
merge (x ∷ vs₀) vs₁ sorted-vs₀ sorted-vs₁ = {!!}
  where
    merged : Sorted-of {!!}
    merged = merge vs₀ vs₁ {!!} {!!}

permTrans-++-hd : ∀ {A : Set} {n m} {a b : Vec A n} {c : Vec A m}
                  → Permutation a b
                  → Permutation (c ++ a) (c ++ b)
permTrans-++-hd {c = Vec.[]} perm = perm
permTrans-++-hd {c = x ∷ c}  perm = permSkip (permTrans-++-hd {c = c} perm)

permTrans-++-tl : ∀ {A : Set} {n m o} {a : Vec A n} {b : Vec A m} {c : Vec A o}
                  → Permutation a b
                  → Permutation (a ++ c) (b ++ c)
permTrans-++-tl {c = c} permEmpty = eqPerm (reflᵥ c)
permTrans-++-tl (permSkip perm) = permSkip (permTrans-++-tl perm)
permTrans-++-tl permSwap = permSwap
permTrans-++-tl {c = tl} (permTrans {a = a} {b} {c} perm₁ perm₂) =
  permTrans {a = a ++ tl} {b = b ++ tl} {c = c ++ tl}
    (permTrans-++-tl perm₁)
    (permTrans-++-tl perm₂)

Sorted-of-refl : ∀ {n} {v : Vec ℕ n}
                 → (S : Sorted-of v)
                 → Sorted-of (Sorted-of.vec S)
Sorted-of-refl sorted = record { vec = Sorted-of.vec sorted
                               ; ordered = Sorted-of.ordered sorted
                               ; perm = eqPerm (reflᵥ (Sorted-of.vec sorted))
                               }

merge-sort : ∀ {n} (vs : SVec ℕ n) → Sorted-of (flatten vs)
merge-sort [] = record
                  { len = 0
                  ; vec = V.[]
                  ; ordered = tt
                  ; perm = permEmpty
                  }

merge-sort [ x ] = record
                     { len = 1
                     ; vec = x V.∷ V.[]
                     ; ordered = tt , tt
                     ; perm = permSkip permEmpty
                     }
merge-sort (vl ⊝ vr) =
  record { len = {!!}
         ; vec = Sorted-of.vec IH
         ; ordered = Sorted-of.ordered IH
         ; perm = perm
         }
  where
    IH₀ : Sorted-of (flatten vl)
    IH₀ = merge-sort vl

    IH₁ : Sorted-of (flatten vr)
    IH₁ = merge-sort vr

    IH : Sorted-of (Sorted-of.vec IH₀ ++ Sorted-of.vec IH₁)
    IH = merge (Sorted-of.vec IH₀) (Sorted-of.vec IH₁)
               (Sorted-of-refl IH₀)
               (Sorted-of-refl IH₁)

    perm = {!!}

    -- perm = permTrans (Sorted-of.perm IH)
    --                  (permTrans (permTrans-++-hd {c = Sorted-of.vec IH₀}
    --                                              (Sorted-of.perm IH₁))
    --                             (permTrans-++-tl {c = flatten vr}
    --                                              (Sorted-of.perm IH₀)))
