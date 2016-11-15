module InsertSort where

open import Data.Nat
open import Data.Vec
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary
open import Permutation

1+m≰1+n⇒m≰n : ∀ {m n} → 1 + m ≰ 1 + n → m ≰ n
1+m≰1+n⇒m≰n 1+m≰1+n m≰n with 1+m≰1+n (s≤s m≰n)
... | ()

m≰n⇒n≤m : ∀ {m n} → m ≰ n → n ≤ m
m≰n⇒n≤m {zero}  {_}     m≰n with m≰n z≤n
... | ()
m≰n⇒n≤m {suc m} {zero}  m≰n = z≤n
m≰n⇒n≤m {suc m} {suc n} m≰n = s≤s (m≰n⇒n≤m (1+m≰1+n⇒m≰n m≰n))

insert : ∀ {n} (a : ℕ) (vs : Vec ℕ n)
         → Ordered vs
         → Sorted-of (a ∷ vs)
insert a [] tt = record { vec = [ a ] ; ordered = tt , tt ; perm = permSkip permEmpty }
insert {suc n} a (x ∷ vs) (x≤vs , vs-sorted) with a ≤? x
... | yes a≤x = record { vec     = a ∷ x ∷ vs
                       ; ordered = (a≤x , Less-≤ a≤x x≤vs) , x≤vs , vs-sorted
                       ; perm    = eqPerm refl
                       }
... | no  a≰x = record { vec     = x ∷ Sorted-of.vec IH
                       ; ordered = Perm-≤ (m≰n⇒n≤m a≰x , x≤vs) (Sorted-of.perm IH) , Sorted-of.ordered IH
                       ; perm    = permTrans (permSkip (Sorted-of.perm IH)) permSwap
                       }
  where
    IH : Sorted-of (a ∷ vs)
    IH = insert a vs vs-sorted

insert-sort : ∀ {n} (vs : Vec ℕ n) → Sorted-of vs
insert-sort [] = record { vec = [] ; ordered = tt ; perm = permEmpty }
insert-sort {suc n} (x ∷ vs) =
  record { vec     = Sorted-of.vec IH₁
         ; ordered = Sorted-of.ordered IH₁
         ; perm    = permTrans (Sorted-of.perm IH₁) (permSkip (Sorted-of.perm IH))
         }
  where
    IH : Sorted-of vs
    IH = insert-sort vs

    IH₁ : Sorted-of (x ∷ Sorted-of.vec IH)
    IH₁ = insert x (Sorted-of.vec IH) (Sorted-of.ordered IH)

ex = insert-sort (1 ∷ 10 ∷ 3 ∷ 4 ∷ 4 ∷ 10 ∷ 8 ∷ [])
