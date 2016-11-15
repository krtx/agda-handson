module Demo where

open import Relation.Binary.PropositionalEquality

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 5 _+_
infixl 6 _*_

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero    * m = zero
(suc n) * m = m + n * m

n*0≡0 : ∀ n → n * zero ≡ zero
n*0≡0 zero = refl
n*0≡0 (suc n) = n*0≡0 n

n*1≡n : ∀ n → n * (suc zero) ≡ n
n*1≡n zero = refl
n*1≡n (suc n) = cong suc (n*1≡n n)

n+sm≡sn+m : ∀ n m → n + suc m ≡ suc (n + m)
n+sm≡sn+m zero m = refl
n+sm≡sn+m (suc n) m = cong suc (n+sm≡sn+m n m)

+-comm : ∀ n m → n + m ≡ m + n
+-comm zero m = sym (m+0≡m m)
  where
    m+0≡m : ∀ m → m + zero ≡ m
    m+0≡m zero = refl
    m+0≡m (suc m) = cong suc (m+0≡m m)
+-comm (suc n) m rewrite n+sm≡sn+m m n = cong suc (+-comm n m)

+-assoc : ∀ n m o → n + m + o ≡ n + (m + o)
+-assoc zero _ _ = refl
+-assoc (suc n) m o = cong suc (+-assoc n m o)

n*2≡n+n : ∀ n → n * (suc (suc zero)) ≡ n + n
n*2≡n+n zero = refl
n*2≡n+n (suc n) rewrite n+sm≡sn+m n n = cong (λ x → suc (suc x)) (n*2≡n+n n)

*-distrib-+ˡ : ∀ n m o → n * (m + o) ≡ n * m + n * o
*-distrib-+ˡ zero m o = refl
*-distrib-+ˡ (suc n) m o rewrite sym (+-assoc (m + n * m) o (n * o))
                               | +-assoc m (n * m) o
                               | +-comm (n * m) o
                               | sym (+-assoc m o (n * m))
                               | +-assoc (m + o) (n * m) (n * o)
  = cong (λ x → m + o + x) (*-distrib-+ˡ n m o)

*-distrib-+ʳ : ∀ n m o → (n + m) * o ≡ n * o + m * o
*-distrib-+ʳ n m zero rewrite n*0≡0 (n + m)
                            | n*0≡0 n
                            | n*0≡0 m = refl
*-distrib-+ʳ n m (suc o) = begin
  (n + m) * suc o
    ≡⟨ n*sm≡n+n*m (n + m) o ⟩
  (n + m) + (n + m) * o
    ≡⟨ cong (λ x → n + m + x) (*-distrib-+ʳ n m o) ⟩
  (n + m) + (n * o + m * o)
    ≡⟨ +-assoc n m (n * o + m * o) ⟩
  n + (m + (n * o + m * o))
    ≡⟨ cong (_+_ n) (sym (+-assoc m (n * o) (m * o))) ⟩
  n + (m + n * o + m * o)
    ≡⟨ cong (_+_ n) (cong (λ x → x + m * o) (+-comm m (n * o))) ⟩
  n + (n * o + m + m * o)
    ≡⟨ cong (_+_ n) (+-assoc (n * o) m (m * o)) ⟩
  n + (n * o + (m + m * o))
    ≡⟨ sym (+-assoc n (n * o) (m + m * o)) ⟩
  n + n * o + (m + m * o)
    ≡⟨ cong (λ x → x + (m + m * o)) (sym (n*sm≡n+n*m n o)) ⟩
  n * suc o + (m + m * o)
    ≡⟨ cong (_+_ (n * suc o)) (sym (n*sm≡n+n*m m o)) ⟩
  n * suc o + m * suc o
    ∎
  where
    open ≡-Reasoning

    n*sm≡n+n*m : ∀ n m → n * suc m ≡ n + n * m
    n*sm≡n+n*m zero m = refl
    n*sm≡n+n*m (suc n) m rewrite n*sm≡n+n*m n m
                               | sym (+-assoc m n (n * m))
                               | sym (+-assoc n m (n * m))
                               | +-comm m n = refl

postulate
  A : Set
  a : A
  b : A
  a≡b : a ≡ b

some-lemma : a ≡ b
some-lemma rewrite a≡b = refl

expand : ∀ a b c d → (a + b) * (c + d) ≡ (a * c + b * c) + (a * d + b * d)
expand a b c d = begin
  (a + b) * (c + d)
    ≡⟨ *-distrib-+ˡ (a + b) c d ⟩
  (a + b) * c + (a + b) * d
    ≡⟨ cong (λ x → x + (a + b) * d) (*-distrib-+ʳ a b c) ⟩
  a * c + b * c + (a + b) * d
    ≡⟨ cong (_+_ (a * c + b * c)) (*-distrib-+ʳ a b d) ⟩
  (a * c + b * c) + (a * d + b * d)
    ∎
  where
    open ≡-Reasoning
