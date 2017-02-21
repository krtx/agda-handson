module Day4-answer where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality

--
-- § 4. レコード型
--

--
-- § 4.1. レコード型の基本
--

--
-- レコード型は複数の値を1つにまとめて扱うことのできるデータ型です。例えば
-- 2つの自然数の組は以下のように定義できます。
--

record Point : Set where
  field
    x : ℕ
    y : ℕ

--
-- この宣言では、Point というデータ型と、Point.x 及び Point.y という2つの
-- 射影関数を定義しています。射影関数は、Point 型の値から対応する field を
-- 取り出す関数です。Point 型の値は record 式を用いて以下のように定義できます。
--

p₀ : Point
p₀ = record { x = 1; y = 2 }

--
-- レコード型の値から各 field の値を取り出すには射影関数を使います。Point 型
-- を定義したときに同時に Point.x と Point.y という関数も定義されるので、
-- それらを用いることで値を取り出すことができます。
--

p₀-x : ℕ
p₀-x = Point.x p₀

p₀-y : ℕ
p₀-y = Point.y p₀

--
-- レコード型では constructor キーワードを使ってコンストラクタに使う
-- シンタックスを指定することができます。
--

record Point′ : Set where
  constructor _,_
  field
    x : ℕ
    y : ℕ

p₁ : Point′
p₁ = 1 , 2

-- ==================================================================
-- Exercise: manhattan (★★)
-- Point 型の値を二次元平面上の点とみなし、マンハッタン距離を計算する関数を
-- 定義してください。
-- ==================================================================

manhattan₀ : ℕ → ℕ → ℕ
manhattan₀ n       zero    = n
manhattan₀ zero    m       = m
manhattan₀ (suc n) (suc m) = manhattan₀ n m

manhattan : Point → Point → ℕ
manhattan p₁ p₂ = manhattan₀ (Point.x p₁) (Point.x p₂) +
                  manhattan₀ (Point.y p₁) (Point.y p₂)

-- ==================================================================
-- Exercise: manhattan (★★★)
-- マンハッタン距離が対称的であることを証明してください。
-- ==================================================================

mh-sym₀ : ∀ m n → manhattan₀ m n ≡ manhattan₀ n m
mh-sym₀ zero    zero    = refl
mh-sym₀ zero    (suc n) = refl
mh-sym₀ (suc m) zero    = refl
mh-sym₀ (suc m) (suc n) = mh-sym₀ m n

mh-sym : ∀ p q → manhattan p q ≡ manhattan q p
mh-sym record { x = px ; y = py }
       record { x = qx ; y = qy } = begin
    manhattan₀ px qx + manhattan₀ py qy
      ≡⟨ cong (λ e → e + _) (mh-sym₀ px qx) ⟩
    manhattan₀ qx px + manhattan₀ py qy
      ≡⟨ cong (λ e → (manhattan₀ qx px) + e) (mh-sym₀ py qy) ⟩
    manhattan₀ qx px + manhattan₀ qy py
  ∎
  where
    open ≡-Reasoning

-- ==================================================================
-- Exercise: tri-ineq (★★★★)
-- マンハッタン距離が三角不等式を満たすことを証明してください。ただし、この
-- 問題は面倒な上にレコード型の理解にあまり寄与しないので、スキップすることを
-- 推奨します。
-- ==================================================================

mh-lem₁ : ∀ x y → x + y ≥ manhattan₀ x y
mh-lem₁ zero    zero    = z≤n
mh-lem₁ zero    (suc y) = n≤m+n 0 (suc y)
mh-lem₁ (suc x) zero    rewrite +-right-identity x = n≤m+n 0 (suc x)
mh-lem₁ (suc x) (suc y) rewrite sym (+-assoc x 1 y)
                              | +-comm x 1
  = ≤pred⇒≤ (manhattan₀ x y) (suc (suc (x + y)))
            (≤pred⇒≤ (manhattan₀ x y) (suc (x + y)) (mh-lem₁ x y))

mh-lem₂ : ∀ m n → manhattan₀ m n + n ≥ m
mh-lem₂ zero    zero    = z≤n
mh-lem₂ zero    (suc n) = z≤n
mh-lem₂ (suc m) zero    rewrite +-right-identity m = n≤m+n 0 (suc m)
mh-lem₂ (suc m) (suc n) rewrite sym (+-assoc (manhattan₀ m n) 1 n)
                              | +-comm (manhattan₀ m n) 1
  = s≤s (mh-lem₂ m n)

tri-ineq₀ : ∀ m n o → manhattan₀ m n + manhattan₀ n o ≥ manhattan₀ m o
tri-ineq₀ m zero zero    = mh-lem₁ m zero
tri-ineq₀ m zero (suc o) = mh-lem₁ m (suc o)
tri-ineq₀ zero (suc n) zero = z≤n
tri-ineq₀ zero (suc n) (suc o)
  rewrite +-comm n (manhattan₀ n o)
        | mh-sym₀ n o
  = s≤s (mh-lem₂ o n)
tri-ineq₀ (suc m) (suc n) zero
  rewrite sym (+-assoc (manhattan₀ m n) 1 n)
        | +-comm (manhattan₀ m n) 1
  = s≤s (mh-lem₂ m n)
tri-ineq₀ (suc m) (suc n) (suc o) = tri-ineq₀ m n o

+-≥ : ∀ {x y z w} → x ≥ z → y ≥ w → x + y ≥ z + w
+-≥ {x} {y} {z} {w} x≥z y≥w = begin
    z + w
      ≤⟨ ≥-add-kʳ y w z y≥w ⟩
    z + y
      ≤⟨ ≥-add-kˡ x z y x≥z ⟩
    x + y
  ∎
  where
    open ≤-Reasoning

    ≥-add-kʳ : ∀ m n k → m ≥ n → k + m ≥ k + n
    ≥-add-kʳ m n zero    ge = ge
    ≥-add-kʳ m n (suc k) ge = s≤s (≥-add-kʳ m n k ge)

    ≥-add-kˡ : ∀ m n k → m ≥ n → m + k ≥ n + k
    ≥-add-kˡ m n k ge rewrite +-comm m k
                            | +-comm n k = ≥-add-kʳ m n k ge


swap-4 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
swap-4 a b c d rewrite sym (+-assoc (a + b) c d)
                     | +-assoc a b c
                     | +-comm b c
                     | sym (+-assoc a c b)
                     | +-assoc (a + c) b d = refl

tri-ineq : ∀ {p q r} → manhattan p q + manhattan q r ≥ manhattan p r
tri-ineq {record { x = px ; y = py }}
         {record { x = qx ; y = qy }}
         {record { x = rx ; y = ry }}
  rewrite
    swap-4 (manhattan₀ px qx) (manhattan₀ py qy)
           (manhattan₀ qx rx) (manhattan₀ qy ry)
  = +-≥ (tri-ineq₀ px qx rx) (tri-ineq₀ py qy ry)

--
-- § 4.2. 依存型を伴うレコード型
--

--
-- Agda は依存型が使えるので、レコードの各フィールドの型が、別のフィールドの値
-- に依存することができます。
--
-- 次のデータ型 Even はある自然数が偶数であることを表すデータ型です。
--

data Even : ℕ → Set where
  e-zero : Even zero
  e-suc  : ∀ {n} → Even n → Even (suc (suc n))

--
-- この Even を用いて、偶数のデータ型 Even-number をレコード型として次のように
-- 定義します。
--

record Even-number : Set where
  constructor _even-by_
  field
    n      : ℕ
    n-even : Even n

--
-- Even-number は自然数 n と n が偶数であることの証明をフィールドととしてもつ
-- レコード型です。n が偶数でなければ Even n は示せないため、Even-number は
-- 偶数全体の集合を表す型となります。
--

-- ==================================================================
-- Exercise: twice-e (★★)
-- 自然数を受け取り、それを2倍にする関数 twice-e を定義してください。ただし、
-- 返り値の型は Even-number であるようにしてください。
-- ==================================================================

twice-e : ℕ → Even-number
twice-e zero = zero even-by e-zero
twice-e (suc n) with twice-e n
... | m even-by m-even = suc (suc m) even-by e-suc m-even

-- ==================================================================
-- Exercise: add-ee (★★)
-- 偶数を2つ受け取り、それらの和を返す関数 add-ee を定義してください。ただし、
-- 返り値の型は Even-number であるようにしてください。
-- ==================================================================

add-ee : Even-number → Even-number → Even-number
add-ee (.0 even-by e-zero) (m even-by m-even) = m even-by m-even
add-ee (suc (suc n) even-by e-suc n-even) (m even-by m-even)
  with add-ee (n even-by n-even) (m even-by m-even)
...  | x even-by x-even
  = suc (suc x) even-by e-suc x-even

-- ==================================================================
-- Exercise: add-eo (★★★)
-- Even, Even-number と同様にしてある自然数が奇数であることを表す型 Odd 及び
-- 奇数の型 Odd-number を定義し、偶数と奇数を足して奇数を返す関数 add-eo を
-- 定義してください。
-- ==================================================================

data Odd : ℕ → Set where
  o-one : Odd (suc zero)
  o-suc : ∀ {n} → Odd n → Odd (suc (suc n))

record Odd-number : Set where
  constructor _odd-by_
  field
    n     : ℕ
    n-odd : Odd n

add-eo : Even-number → Odd-number → Odd-number
add-eo (.0 even-by e-zero) m = m
add-eo (suc (suc n) even-by e-suc n-even) m with add-eo (n even-by n-even) m
...  | x odd-by x-odd = suc (suc x) odd-by o-suc x-odd
