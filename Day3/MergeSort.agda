module MergeSort where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
import Data.Fin as F
open import Data.Vec as V using (Vec; _++_; _∷_)
open import Permutation
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

merge : ∀ {n m} (vs₀ : Vec ℕ n) (vs₁ : Vec ℕ m)
        → Sorted-of vs₀
        → Sorted-of vs₁
        → Sorted-of (vs₀ ++ vs₁)
merge Vec.[] vs₁ sorted-vs₀ sorted-vs₁ = sorted-vs₁
merge vs₀ Vec.[] sorted-vs₀ sorted-vs₁ = {!!}
merge (x ∷ vs₀) (y ∷ vs₁) sorted-vs₀ sorted-vs₁ = {!!}

permTrans-++-hd : ∀ {A : Set} {n m} {a b : Vec A n} {c : Vec A m}
                  → Permutation a b
                  → Permutation (c ++ a) (c ++ b)
permTrans-++-hd {c = Vec.[]} perm = perm
permTrans-++-hd {c = x ∷ c}  perm = permSkip (permTrans-++-hd {c = c} perm)

permTrans-++-tl : ∀ {A : Set} {n m} {a b : Vec A n} {c : Vec A m}
                  → Permutation a b
                  → Permutation (a ++ c) (b ++ c)
permTrans-++-tl permEmpty = eqPerm refl
permTrans-++-tl permSwap  = permSwap
permTrans-++-tl {c = c} (permSkip perm) =
  permSkip (permTrans-++-tl {c = c} perm)
permTrans-++-tl {c = c} (permTrans perm₁ perm₂) =
  permTrans (permTrans-++-tl {c = c} perm₁)
            (permTrans-++-tl {c = c} perm₂)

Sorted-of-refl : ∀ {n} {v : Vec ℕ n}
                 → (S : Sorted-of v)
                 → Sorted-of (Sorted-of.vec S)
Sorted-of-refl sorted = record { vec = Sorted-of.vec sorted
                               ; ordered = Sorted-of.ordered sorted
                               ; perm = eqPerm refl }

merge-sort : ∀ {n} (vs : SVec ℕ n) → Sorted-of (flatten vs)
merge-sort [] = record
                  { vec = V.[]
                  ; ordered = tt
                  ; perm = permEmpty
                  }

merge-sort [ x ] = record
                     { vec = x V.∷ V.[]
                     ; ordered = tt , tt
                     ; perm = permSkip permEmpty
                     }
merge-sort (vl ⊝ vr) =
  record { vec = Sorted-of.vec IH
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

    perm = permTrans (Sorted-of.perm IH)
                     (permTrans (permTrans-++-hd {c = Sorted-of.vec IH₀}
                                                 (Sorted-of.perm IH₁))
                                (permTrans-++-tl {c = flatten vr}
                                                 (Sorted-of.perm IH₀)))
