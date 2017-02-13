module Day4 where

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

manhattan : Point → Point → ℕ
manhattan = {!!}

-- ==================================================================
-- Exercise: manhattan (★★★)
-- マンハッタン距離が対称的であることを証明してください。
-- ==================================================================

mh-sym : ∀ p q → manhattan p q ≡ manhattan q p
mh-sym = {!!}

-- ==================================================================
-- Exercise: tri-ineq (★★★★)
-- マンハッタン距離が三角不等式を満たすことを証明してください。ただし、この
-- 問題は面倒な上にレコード型の理解にあまり寄与しないので、スキップすることを
-- 推奨します。
-- ==================================================================

tri-ineq : ∀ {p q r} → manhattan p q + manhattan q r ≥ manhattan p r
tri-ineq = {!!}

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
twice-e = {!!}

-- ==================================================================
-- Exercise: add-ee (★★)
-- 偶数を2つ受け取り、それらの和を返す関数 add-ee を定義してください。ただし、
-- 返り値の型は Even-number であるようにしてください。
-- ==================================================================

add-ee : Even-number → Even-number → Even-number
add-ee = {!!}

-- ==================================================================
-- Exercise: add-eo (★★★)
-- Even, Even-number と同様にしてある自然数が奇数であることを表す型 Odd 及び
-- 奇数の型 Odd-number を定義し、偶数と奇数を足して奇数を返す関数 add-eo を
-- 定義してください。
-- ==================================================================

--
-- data Odd : ℕ → Set where
--   ...
--
--
-- record Odd-number : Set where
--   ...
--
-- add-eo : Even-number → Odd-number → Odd-number
-- add-eo = ?
--
