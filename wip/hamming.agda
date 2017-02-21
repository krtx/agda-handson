module hamming where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

hamming : ∀ {n} → Vec ℕ n → Vec ℕ n → ℕ
hamming []       []       = 0
hamming (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes p  = hamming xs ys
... | no  ¬p = suc (hamming xs ys)

hm-sym : ∀ {n} (xs ys : Vec ℕ n) → hamming xs ys ≡ hamming ys xs
hm-sym []       []       = refl
hm-sym (x ∷ xs) (y ∷ ys) with x ≟ y | y ≟ x
... | yes _ | yes _ = hm-sym xs ys
... | no  _ | no  _ = cong suc (hm-sym xs ys)
hm-sym (x ∷ xs) (y ∷ ys) | yes p | no  q with q (sym p)
... | ()
hm-sym (x ∷ xs) (y ∷ ys) | no  p | yes q with p (sym q)
... | ()

suc-right : ∀ {x y} → x ≤ y → x ≤ suc y
suc-right {x} {y} x≤y = begin
  x     ≤⟨ x≤y ⟩
  y     ≤⟨ n≤1+n y ⟩
  suc y ∎
  where
    open ≤-Reasoning

swap-3 : ∀ n m o → n + (m + o) ≡ m + n + o
swap-3 n m o rewrite sym (+-assoc n m o) | +-comm n m = refl

hm-tri : ∀ {n} (xs ys zs : Vec ℕ n) → hamming xs ys + hamming ys zs ≥ hamming xs zs
hm-tri [] [] [] = z≤n
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) with x ≟ y | y ≟ z | x ≟ z
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | yes p | yes q | yes r = hm-tri xs ys zs
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | yes p | yes q | no  r with r (trans p q)
... | ()
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | yes p | no  q | yes r with q (trans (sym p) r)
... | ()
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | yes p | no  q | no  r
  rewrite swap-3 (hamming xs ys) 1 (hamming ys zs) = s≤s (hm-tri xs ys zs)
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | no  p | yes q | yes r with p (trans r (sym q))
... | ()
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | no  p | yes q | no  r = s≤s (hm-tri xs ys zs)
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | no  p | no  q | yes r
  rewrite swap-3 (hamming xs ys) 1 (hamming ys zs) = suc-right (suc-right (hm-tri xs ys zs))
hm-tri (x ∷ xs) (y ∷ ys) (z ∷ zs) | no  p | no  q | no  r
  rewrite swap-3 (hamming xs ys) 1 (hamming ys zs) = s≤s (suc-right (hm-tri xs ys zs))
