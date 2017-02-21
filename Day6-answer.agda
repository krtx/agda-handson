module Day5-answer where

open import Data.List
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

data Perm {A : Set} : List A → List A → Set where
  p-empty : Perm [] []
  p-skip  : ∀ {l₁ l₂ : List A} {h}
            → Perm l₁ l₂
            → Perm (h ∷ l₁) (h ∷ l₂)
  p-swap  : ∀ {l : List A} {x y}
            → Perm (x ∷ y ∷ l) (y ∷ x ∷ l)
  p-trans : ∀ {l₁ l₂ l₃ : List A}
            → Perm l₁ l₂
            → Perm l₂ l₃
            → Perm l₁ l₃

data Less : ℕ → List ℕ → Set where
  l-nil  : ∀ {x} → Less x []
  l-cons : ∀ {a x} {xs} → a ≤ x → Less a xs → Less a (x ∷ xs)

data Ordered : List ℕ → Set where
  o-nil  : Ordered []
  o-cons : ∀ {x} {xs} → Less x xs → Ordered xs → Ordered (x ∷ xs)

record Sorted-of (xs′ : List ℕ) : Set where
  field
    xs      : List ℕ
    ordered : Ordered xs
    perm    : Perm xs xs′

p-refl : ∀ {A : Set} {xs : List A} → Perm xs xs
p-refl {xs = []}     = p-empty
p-refl {xs = _ ∷ xs} = p-skip (p-refl {xs = xs})

p-sym : ∀ {A : Set} {xs ys : List A} → Perm xs ys → Perm ys xs
p-sym p-empty               = p-empty
p-sym (p-skip perm)         = p-skip (p-sym perm)
p-sym p-swap                = p-swap
p-sym (p-trans perm₁ perm₂) = p-trans (p-sym perm₂) (p-sym perm₁)

Less-≤ : ∀ {a b} {l} → a ≤ b → Less b l → Less a l
Less-≤ a≤b l-nil           = l-nil
Less-≤ a≤b (l-cons b≤x le) = l-cons (≤-trans a≤b b≤x) (Less-≤ a≤b le)

Perm-≤ : ∀ {a xs ys} → Less a xs → Perm xs ys → Less a ys
Perm-≤ l-nil                        p-empty               = l-nil
Perm-≤ (l-cons a≤h le)              (p-skip perm)         = l-cons a≤h (Perm-≤ le perm)
Perm-≤ (l-cons a≤x (l-cons a≤y le)) p-swap                = l-cons a≤y (l-cons a≤x le)
Perm-≤ le                           (p-trans perm₁ perm₂) = Perm-≤ (Perm-≤ le perm₁) perm₂

1+m≰1+n⇒m≰n : ∀ {m n} → 1 + m ≰ 1 + n → m ≰ n
1+m≰1+n⇒m≰n 1+m≰1+n m≰n with 1+m≰1+n (s≤s m≰n)
... | ()

m≰n⇒n≤m : ∀ {m n} → m ≰ n → n ≤ m
m≰n⇒n≤m {zero}  {_}     m≰n with m≰n z≤n
... | ()
m≰n⇒n≤m {suc m} {zero}  m≰n = z≤n
m≰n⇒n≤m {suc m} {suc n} m≰n = s≤s (m≰n⇒n≤m (1+m≰1+n⇒m≰n m≰n))

insert : ∀ (a : ℕ) (xs : List ℕ) → Ordered xs → Sorted-of (a ∷ xs)
insert a [] o-nil = record { xs      = a ∷ []
                           ; ordered = o-cons l-nil o-nil
                           ; perm    = p-skip p-empty }
insert a (x ∷ xs) (o-cons x≤xs ordered) with a ≤? x
... | yes a≤x = record { xs      = a ∷ x ∷ xs
                       ; ordered = o-cons (l-cons a≤x (Less-≤ a≤x x≤xs))
                                          (o-cons x≤xs ordered)
                       ; perm    = p-refl }
... | no  a≰x = record { xs      = x ∷ Sorted-of.xs IH
                       ; ordered = o-cons (Perm-≤ (l-cons (m≰n⇒n≤m a≰x) x≤xs)
                                                  (p-sym (Sorted-of.perm IH)))
                                          (Sorted-of.ordered IH)
                       ; perm    = p-trans (p-skip (Sorted-of.perm IH))
                                           p-swap
                       }
  where
    IH : Sorted-of (a ∷ xs)
    IH = insert a xs ordered

insert-sort : ∀ (xs : List ℕ) → Sorted-of xs
insert-sort [] = record { xs = [] ; ordered = o-nil ; perm = p-empty }
insert-sort (x ∷ xs) =
  record { xs      = Sorted-of.xs IH₀
         ; ordered = Sorted-of.ordered IH₀
         ; perm    = p-trans (Sorted-of.perm IH₀)
                             (p-skip (Sorted-of.perm IH)) }
  where
    IH : Sorted-of xs
    IH = insert-sort xs

    IH₀ : Sorted-of (x ∷ Sorted-of.xs IH)
    IH₀ = insert x (Sorted-of.xs IH) (Sorted-of.ordered IH)
