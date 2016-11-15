--
-- 目次:
-- § 3. List
-- § 3.1 List の定義
-- § 3.2 List 上の関数
-- § 3.3 List に関する証明
-- § 4. 長さの制限つきの List (Vec)

module Day3 where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Bool
open import Data.Empty
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

--
--
--
-- § 3. リスト
--
--
--

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

ex₁ : List ℕ
ex₁ = 0 ∷ 1 ∷ 2 ∷ []

ex₂ : List ℕ
ex₂ = 3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ []

ex₃ : List Bool
ex₃ = true ∷ false ∷ false ∷ true ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

ex₄ : List ℕ
ex₄ = ex₁ ++ ex₂ -- C-c C-n ex₄ で ex₄ を確認しよう

app-nil : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
app-nil []       = refl
app-nil (x ∷ xs) = cong (_∷_ x) (app-nil xs)

app-assoc : ∀ {A : Set} (xs ys zs : List A)
            → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
app-assoc []       ys zs = refl
app-assoc (x ∷ xs) ys zs = cong (_∷_ x) (app-assoc xs ys zs)

rev : ∀ {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = (rev xs) ++ (x ∷ [])

rev-app : ∀ {A : Set} (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-app [] ys = sym (app-nil (rev ys))
rev-app (x ∷ xs) ys rewrite app-assoc (rev ys) (rev xs) (x ∷ [])
  = cong (λ xs → xs ++ x ∷ []) (rev-app xs ys)

rev-involutive : ∀ {A : Set} (xs : List A) → rev (rev xs) ≡ xs
rev-involutive [] = refl
rev-involutive (x ∷ xs) = begin
  rev (rev xs ++ x ∷ [])
    ≡⟨ rev-app (rev xs) (x ∷ []) ⟩
  rev (x ∷ []) ++ rev (rev xs)
    ≡⟨ cong (_∷_ x) (rev-involutive xs) ⟩
  x ∷ xs
    ∎
  where
    open ≡-Reasoning

equiv-cons : ∀ {A : Set} {x y : A} {xs ys : List A}
             → x ∷ xs ≡ y ∷ ys
             → x ≡ y × xs ≡ ys
equiv-cons refl = refl , refl

equiv-snoc : ∀ {A : Set} {x y : A} (xs ys : List A)
            → xs ++ x ∷ [] ≡ ys ++ y ∷ []
            → xs ≡ ys × x ≡ y
equiv-snoc []          []          refl = refl , refl
equiv-snoc []          (_ ∷ [])    ()
equiv-snoc []          (_ ∷ _ ∷ _) ()
equiv-snoc (_ ∷ [])    []          ()
equiv-snoc (_ ∷ _ ∷ _) []          ()
equiv-snoc (x ∷ xs) (y ∷ ys) eq with equiv-cons eq
... | eq₁ , eq₂ rewrite eq₁
  = cong (_∷_ y) (proj₁ (equiv-snoc xs ys eq₂)) ,
    (proj₂ (equiv-snoc xs ys eq₂))

rev-injective : ∀ {A : Set} (xs ys : List A) → rev xs ≡ rev ys → xs ≡ ys
rev-injective [] [] eq = refl
rev-injective [] (x ∷ ys) eq with rev ys
rev-injective [] (_ ∷ _) () | []
rev-injective [] (_ ∷ _) () | _ ∷ _
rev-injective (x ∷ xs) [] eq with rev xs
rev-injective (x ∷ xs) [] () | []
rev-injective (x ∷ xs) [] () | _ ∷ _
rev-injective (x ∷ xs) (y ∷ ys) eq with equiv-snoc (rev xs) (rev ys) eq
... | eq₁ , eq₂ rewrite rev-injective xs ys eq₁ | eq₂ = refl

rev-injective' : ∀ {A : Set} (xs ys : List A) → rev xs ≡ rev ys → xs ≡ ys
rev-injective' xs ys eq rewrite sym (rev-involutive xs)
                              | sym (rev-involutive ys)
                              | rev-involutive (rev xs)
                              | rev-involutive (rev ys) = cong rev eq

length : ∀ {A : Set} → List A → ℕ
length []       = 0
length (_ ∷ xs) = suc (length xs)

-- with の説明
filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter _ [] = []
filter f (x ∷ xs) with f x
filter f (x ∷ xs) | false = filter f xs
filter f (x ∷ xs) | true = x ∷ filter f xs

filter-app : ∀ {A : Set} {f : A → Bool} {xs ys : List A}
             → filter f (xs ++ ys) ≡ filter f xs ++ filter f ys
filter-app {xs = []} = refl
filter-app {f = f} {xs = x ∷ xs} with f x
filter-app {A} {f} {x ∷ xs} | false = filter-app {xs = xs}
filter-app {A} {f} {x ∷ xs} | true = cong (_∷_ x) (filter-app {xs = xs})

app-length : ∀ {A : Set} {xs ys : List A} → length (xs ++ ys) ≡ length xs + length ys
app-length {xs = []} = refl
app-length {xs = x ∷ xs} = cong suc (app-length {xs = xs})

rev-length : ∀ {A : Set} {xs : List A} → length (rev xs) ≡ length xs
rev-length {xs = []} = refl
rev-length {xs = x ∷ xs}
  rewrite app-length {xs = rev xs} {ys = x ∷ []}
          | +-comm (length (rev xs)) 1
  = cong suc (rev-length {xs = xs})

evenb : ℕ → Bool
oddb  : ℕ → Bool

evenb 0 = true
evenb (suc n) = oddb n

oddb 0 = false
oddb (suc n) = evenb n

filter-example₁ : List ℕ
filter-example₁ = filter evenb (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

map-length : ∀ {A B : Set} (f : A → B) (xs : List A)
             → length xs ≡ length (map f xs)
map-length f []       = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

filter-≤ : ∀ {A : Set} (f : A → Bool) (xs : List A) → length (filter f xs) ≤ length xs
filter-≤ f [] = z≤n
filter-≤ f (x ∷ xs) with f x
filter-≤ f (x ∷ xs) | false = ≤-steps 1 (filter-≤ f xs)
filter-≤ f (x ∷ xs) | true  = s≤s (filter-≤ f xs)

filter-idempotent : ∀ {A : Set} (f : A → Bool) (xs : List A)
                    → filter f (filter f xs) ≡ filter f xs
filter-idempotent f [] = refl
filter-idempotent f (x ∷ xs) with f x | inspect f x
filter-idempotent f (x ∷ xs) | false | [ _ ] = filter-idempotent f xs
filter-idempotent f (x ∷ xs) | true  | [ _ ] with f x | inspect f x
filter-idempotent f (x ∷ xs) | true  | [ () ] | false | _
filter-idempotent f (x ∷ xs) | true  | [ _ ]  | true  | [ _ ] =
  cong (_∷_ x) (filter-idempotent f xs)

infix 4 _∈_

data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {x xs} → x ∈ x ∷ xs
  there : ∀ {x y xs} → x ∈ xs → x ∈ y ∷ xs

beq-nat : ℕ → ℕ → Bool
beq-nat zero    zero    = true
beq-nat zero    (suc _) = false
beq-nat (suc _) zero    = false
beq-nat (suc m) (suc n) = beq-nat m n

-- absurd pattern の説明
beq-nat-eqv : ∀ {n m} → beq-nat n m ≡ true → n ≡ m
beq-nat-eqv {zero}  {zero}  eqb = refl
beq-nat-eqv {zero}  {suc m} ()
beq-nat-eqv {suc n} {zero}  ()
beq-nat-eqv {suc n} {suc m} eqb = cong suc (beq-nat-eqv {n} {m} eqb)

filter-not-empty-in : ∀ {n xs} → filter (beq-nat n) xs ≢ [] → n ∈ xs
filter-not-empty-in {xs = []} p with p refl
... | ()
filter-not-empty-in {n} {x ∷ xs} p with beq-nat n x | inspect (beq-nat n) x
filter-not-empty-in {n} {x ∷ xs} p | false | [ _ ] = there (filter-not-empty-in {xs = xs} p)
filter-not-empty-in {n} {x ∷ xs} p | true | [ eq ] rewrite beq-nat-eqv {n} {x} eq = here

infix 4 _⊆_

data _⊆_ {A : Set} : List A → List A → Set where
  nil  : [] ⊆ []
  skip : ∀ {x xs ys} → xs ⊆ ys →     xs ⊆ x ∷ ys
  cons : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  
l₁ : List ℕ
l₁ = 1 ∷ 2 ∷ []

l₂ : List ℕ
l₂ = 1 ∷ 2 ∷ 3 ∷ []

example₁ : l₁ ⊆ l₂
example₁ = cons (cons (skip nil))

filter-⊆ : ∀ {A : Set} (f : A → Bool) (xs : List A) → filter f xs ⊆ xs
filter-⊆ f [] = nil
filter-⊆ f (x ∷ xs) with f x
filter-⊆ f (x ∷ xs) | false = skip (filter-⊆ f xs)
filter-⊆ f (x ∷ xs) | true = cons (filter-⊆ f xs)

infix 4 _⊆′_

_⊆′_ : ∀ {A : Set} → List A → List A → Set
_⊆′_ xs ys = ∀ {x} → x ∈ xs → x ∈ ys

l₃ : List ℕ
l₃ = 2 ∷ 3 ∷ 1 ∷ []

example₂ : l₁ ⊆′ l₃
example₂ here               = there (there here)
example₂ (there here)       = here
example₂ (there (there ()))

⊆⇒⊆′ : ∀ {A : Set} {xs ys : List A} → xs ⊆ ys → xs ⊆′ ys
⊆⇒⊆′ nil          x∈xs         = x∈xs
⊆⇒⊆′ (skip xs⊆ys) x∈xs         = there (⊆⇒⊆′ xs⊆ys x∈xs)
⊆⇒⊆′ (cons _)     here         = here
⊆⇒⊆′ (cons xs⊆ys) (there x∈xs) = there (⊆⇒⊆′ xs⊆ys x∈xs)

12⊆′21 : 1 ∷ 2 ∷ [] ⊆′ 2 ∷ 1 ∷ []
12⊆′21 here               = there here
12⊆′21 (there here)       = here
12⊆′21 (there (there ()))

⊆′⇏⊆ : ¬ (∀ {A : Set} {xs ys : List A} → xs ⊆′ ys → xs ⊆ ys)
⊆′⇏⊆ ⊆′⇒⊆ with ⊆′⇒⊆ {xs = 1 ∷ 2 ∷ []} {ys = 2 ∷ 1 ∷ []} 12⊆′21
... | skip (skip ())
... | skip (cons ())

data Permutation {A : Set} : List A → List A → Set where
  perm-empty : Permutation [] []
  perm-skip  : ∀ {x l₁ l₂}
               → Permutation l₁ l₂
               → Permutation (x ∷ l₁) (x ∷ l₂)
  perm-swap  : ∀ {x y l}
               → Permutation (x ∷ y ∷ l) (y ∷ x ∷ l)
  perm-trans : ∀ {l₁ l₂ l₃}
               → Permutation l₁ l₂
               → Permutation l₂ l₃
               → Permutation l₁ l₃

data Palindrome {A : Set} : List A → Set where
  nil : Palindrome []
  singleton : ∀ {x} → Palindrome (x ∷ [])
  cons : ∀ {x xs} → Palindrome xs → Palindrome (x ∷ xs ++ x ∷ [])

pal-app-rev : ∀ {A : Set} (xs : List A) → Palindrome (xs ++ rev xs)
pal-app-rev [] = nil
pal-app-rev (x ∷ xs) rewrite app-assoc (x ∷ xs) (rev xs) (x ∷ []) =
  cons {xs = xs ++ rev xs} (pal-app-rev xs)

