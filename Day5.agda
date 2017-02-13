module Day5 where

open import Data.List
open import Data.Nat

--
-- 挿入ソートが正しいことを証明してください。ここでは、ソートアルゴリズムが
-- 正しいことを以下の2つの条件を満たすこととします。
--
--   1. 返り値のリストが昇順になっていること
--   2. 返り値のリストが元のリストの順列になっていること
--
-- 1. の条件はすぐ思いつくものですが、2. の条件も重要です。2. がなければ、
-- 入力を無視して単に空リストを返す関数でも正しいソートアルゴリズムであること
-- を証明できてしまいます。
--
-- まず、ある自然数 x とあるリスト xs について、x が xs のすべての要素以下で
-- あることを表すデータ型 Less を以下のように定義します。
--

data Less : ℕ → List ℕ → Set where
  l-nil  : ∀ {x} → Less x []
  l-cons : ∀ {a x} {xs} → a ≤ x → Less a xs → Less a (x ∷ xs)

--
-- Less を用いて、あるリストが昇順であることを表すデータ型 Ordered を以下の
-- ように定義します。
--

data Ordered : List ℕ → Set where
  o-nil  : Ordered []
  o-cons : ∀ {x} {xs} → Less x xs → Ordered xs → Ordered (x ∷ xs)

--
-- ある2つのリストが順列であることを表すデータ型 Perm は以下のように定義します。
-- この定義は [1] を参考にしました。
--

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

--
-- Ordered と Perm を用いて、ソートアルゴリズムが正しいことを次のデータ型
-- Sorted-of によって表現します。あるリスト xs について Sorted-of xs
-- という型は、xs をソートした結果のリスト、その結果が昇順であること、さらに
-- xs の順列になっていること、をフィールドとしてもつレコードです。
--

record Sorted-of (xs′ : List ℕ) : Set where
  field
    xs      : List ℕ
    ordered : Ordered xs
    perm    : Perm xs xs′

-- ==================================================================
-- Exercise: 正しいソートアルゴリズムを定義してください。
--
-- ヒント:
--   O(n²) のアルゴリズムを想定しています。まず 1ステップ毎の挿入(insert)が
--   正しいことを証明し(正しい挿入アルゴリズムを定義し)、それを使って
--   insert-sort を証明してください。insert の型が重要になります。
--
--   Less や Perm などに関して補題がいくつか必要になります。その際、単に必要な
--   命題をそのまま証明しようとするのではなく、一般的な形を考えるようにしてくだ
--   さい。
--
--   大小比較には Data.Nat.≤? を使ってください(説明がなくてすみません...)。
-- ==================================================================

insert-sort : ∀ (xs : List ℕ) → Sorted-of xs
insert-sort = {!!}

--
-- Reference
-- [1] https://github.com/pi8027/sandpit/blob/master/agda/Relation/Binary/Permutation.agda
--
