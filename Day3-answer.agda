module Day3-answer where

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
-- § 3.1 リストの定義と簡単な操作
--

--
-- リストは次のように定義されます。
--

infixr 5 _∷_ -- 右結合

data List (A : Set) : Set where
  []  : List A                   -- 要素をもたない空のリスト (nil)
  _∷_ : A → List A → List A      -- 先頭に要素を1つ追加するコンストラクタ (cons)

--
-- リストの例です。以下はいわゆる [1, 5, 9] ですが、Agda ではリストを
-- このようにリテラルとして記述する方法は提供されていません（おそらく）。
--

list-example₁ : List ℕ
list-example₁ = 1 ∷ 5 ∷ 9 ∷ []

list-example₂ : List Bool
list-example₂ = true ∷ false ∷ true ∷ true ∷ []

--
-- このリストの定義では、以下のようなリストは当然ですが型エラーになります。
--

--
-- list-example-fail : List ℕ
-- list-example-fail = 1 ∷ false ∷ []
--

--
-- リスト同士を連結する関数 append は以下のように定義されます。
--

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

--
-- C-c C-n list-example₃ で list-example₃ を確認してください。
--

list-example₃ : List ℕ
list-example₃ = 3 ∷ 1 ∷ 4 ∷ [] ++ 1 ∷ 5 ∷ []

-- ==================================================================
-- Exercise: (2 star) app-nil
-- 右から nil を結合したリストは元のリストと同じであることを証明してください。
-- ==================================================================

app-nil : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
app-nil []       = refl
app-nil (x ∷ xs) = cong (_∷_ x) (app-nil xs)

-- ==================================================================
-- Exercise: (2 star) app-assoc
-- _++_ の結合法則を証明してください。_++_ は右結合なので、xs ++ ys ++ zs
-- は xs ++ (ys ++ zs) と解釈されます。
-- ==================================================================

app-assoc : ∀ {A : Set} (xs ys zs : List A)
            → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
app-assoc []       ys zs = refl
app-assoc (x ∷ xs) ys zs = cong (_∷_ x) (app-assoc xs ys zs)

--
-- rev はリストを逆順にする関数です。
--

rev : ∀ {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = (rev xs) ++ (x ∷ [])

list-example₄ : List ℕ
list-example₄ = rev list-example₃ -- C-c C-n で確認

-- ==================================================================
-- Exercise: (3 star) rev-involutive
-- 2回 rev を適用すると元に戻ることを証明してください。適切な補題を用意すると
-- 証明を見通しよく進めることができます。
-- ==================================================================

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

-- ==================================================================
-- Exercise: (5 star) rev-injective
-- rev が単射であることを証明してください。素直にやろうとすると難しいですが、
-- 上手なやり方があります。いずれにせよ難しいので、分からなかったら飛ばして
-- ください。
-- ==================================================================

rev-injective : ∀ {A : Set} (xs ys : List A) → rev xs ≡ rev ys → xs ≡ ys
rev-injective xs ys eq rewrite sym (rev-involutive xs)
                             | sym (rev-involutive ys)
                             | rev-involutive (rev xs)
                             | rev-involutive (rev ys) = cong rev eq

--
-- 別解: xs と ys に関する帰納法
--

open import Data.Product

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

rev-injective′ : ∀ {A : Set} (xs ys : List A) → rev xs ≡ rev ys → xs ≡ ys
rev-injective′ [] [] eq = refl
rev-injective′ [] (x ∷ ys) eq with rev ys
rev-injective′ [] (_ ∷ _) () | []
rev-injective′ [] (_ ∷ _) () | _ ∷ _
rev-injective′ (x ∷ xs) [] eq with rev xs
rev-injective′ (x ∷ xs) [] () | []
rev-injective′ (x ∷ xs) [] () | _ ∷ _
rev-injective′ (x ∷ xs) (y ∷ ys) eq with equiv-snoc (rev xs) (rev ys) eq
... | eq₁ , eq₂ rewrite rev-injective′ xs ys eq₁ | eq₂ = refl

--
-- § 3.2 With-Abstraction
-- 
-- わからないところがあったら
-- http://agda.readthedocs.io/en/latest/language/with-abstraction.html
-- を参照してください
--

--
-- リストをフィルターする関数を考えます。まず、偶数かどうかを判定する関数 evenb
-- が次のように定義されているとします。
--

evenb : ℕ → Bool
evenb 0 = true
evenb (suc n) = not (evenb n)

--
-- リスト xs と真偽値を返す関数 f が与えられたとき、filter f xs は xs のうち
-- f を適用すると真になる値だけを集めたリストを返すように定義します。たとえば、
-- 偶数かどうかを判定する関数 evenb を使うとリスト中の偶数の要素だけを集める
-- ことができます。
--
--   filter evenb (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) => 2 ∷ 4 ∷ []
--
-- filter の定義を途中まで書くと次のようになります。
--
--   filter : ∀ {A : Set} → (A → Bool) → List A → List A
--   filter _ [] = []
--   filter f (x ∷ xs) = ?
--
-- ここで、f を x に適用した結果について場合分けする必要があります。
-- if_then_else_ を使えば次のように書けます（if_then_else_ の定義を
-- 思い出しましょう）。
--

filter₀ : ∀ {A : Set} → (A → Bool) → List A → List A
filter₀ _ [] = []          -- 値を使わないときは _ で捨てることができます
filter₀ f (x ∷ xs) = if
                       f x
                     then
                       x ∷ filter₀ f xs
                     else
                       filter₀ f xs

--
-- ですが、Agda には f x のようにこれから計算されるような項に対してもパターン
-- マッチによって場合分けする方法があります。それを実現するのが with-abstraction
-- です。
--

filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter _ [] = []
filter f (x ∷ xs) with f x                  -- 1. f x の結果についてパターンマッチ
filter f (x ∷ xs) | false = filter f xs     -- 2. f x が false の場合
filter f (x ∷ xs) | true  = x ∷ filter f xs -- 3. f x が true の場合

--
-- 1. では引数をすべて書いた続きに with f x と記述し、右辺は書かず改行します。
-- 2. と 3. が実際の各値に対する定義を書く行で、いずれも | の後にパターンマッチの
-- 結果、続いて右辺（関数本体）を記述します。
--
-- 引数の名前などが変わらない場合は、左辺を ... によって省略することもできます。
--

filter′ : ∀ {A : Set} → (A → Bool) → List A → List A
filter′ _ [] = []
filter′ f (x ∷ xs) with f x
...                   | false = filter′ f xs
...                   | true  = x ∷ filter′ f xs

-- ==================================================================
-- Exercise: (3 star) filter-app
-- xs に関する帰納法によって証明してください。with を使う必要があります。
-- ==================================================================

filter-app : ∀ {A : Set} (f : A → Bool) (xs ys : List A)
             → filter f (xs ++ ys) ≡ filter f xs ++ filter f ys
filter-app f []       ys = refl
filter-app f (x ∷ xs) ys with f x
...                         | false = filter-app f xs ys
...                         | true  = cong (_∷_ x) (filter-app f xs ys)
