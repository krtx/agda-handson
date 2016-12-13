module Day3 where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool

--
--
--
-- § 3. リスト
--
--
--

--
-- リストは次のように定義されます。
--

infixr 5 _∷_ -- 右結合

data List (A : Set) : Set where
  []  : List A                   -- 要素をもたない空のリスト (nil)
  _∷_ : A → List A → List A      -- 先頭に要素を1つ追加するコンストラクタ (cons)

--
-- § 3.1.1 リストの例 
--

--
-- 以下はいわゆる [1, 5, 9] ですが、Agda ではリストをこのようにリテラルとして記述
-- する方法は提供されていません（おそらく）。
--

list-example₁ : List ℕ
list-example₁ = 1 ∷ 5 ∷ 9 ∷ []

list-example₂ : List Bool
list-example₂ = true ∷ false ∷ true ∷ true ∷ []

--
-- このリストの定義だと以下のようにヘテロなリストは当然ですが型エラーになります。
--

--
-- list-example-fail : List ℕ
-- list-example-fail = 1 ∷ false ∷ []
--

--
-- § 3.1.2 リスト同士の結合 (append)
--

