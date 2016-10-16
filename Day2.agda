module Day2 where

open import Data.Nat

-- List の説明

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

-- Vec の説明

data Vec (A : Set) : ℕ → Set where
  nil  : Vec A 0
  cons : ∀ {n} → A → Vec A n → Vec A (suc n)

-- record の説明

record _×_ {A B : Set} : Set where
  constructor _,_
  field
    inj₁ : A
    inj₂ : B


data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

-- absurd pattern の説明
-- with の説明
