module Day2-answer where


--
--
--
-- § 2. +-comm Revisited
--
--
--
-- Day1 で証明した +-comm の別証を通して Agda の機能を解説します。異なる
-- 証明といっても、（いわゆる紙とペンによる）証明の方針が違うわけではなく
-- Agda の機能の解説が主目的です。
--

open import Relation.Binary.PropositionalEquality

--
-- この章では、自然数は標準ライブラリとして提供されているものを使います。
--

open import Data.Nat

--
-- 標準ライブラリでの自然数の定義は Day1 で定義したものとほぼ同じですが、
-- 整数リテラルを用いた自然数の表記が可能です。
--

the-answer-of-bla-bla-bla : ℕ
the-answer-of-bla-bla-bla = 42

--
-- n≡n+0 などの必要な補題を証明します。ところで、Day1 で定義した
-- cong-suc は次のような命題でした。
--
--   cong-suc : ∀ n m → n ≡ m → suc n ≡ suc m
--
-- この cong-suc について、suc を一般化した cong という命題が
-- Relation.Binary.PropositionalEquality に定義されています。
--
--   cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
--
-- 引数が implicit になっていること、suc が f として一般化されているという
-- 違いがあります。引数が implicit になっているという違いを除いて、cong-suc
-- は cong suc と同等です。以下の n≡n+0 の定義を Day1 のものと比べてみて
-- ください。
--

n≡n+0 : ∀ n → n ≡ n + 0
n≡n+0 zero    = refl
n≡n+0 (suc n) = cong suc (n≡n+0 n)

--
-- cong の引数 f はいちいち定義してもいいですが、匿名関数を使ったほうが便利です。
-- Agda では匿名関数は \ x → (関数本体) または λ x → (関数本体) で定義できます。
--

ex-cong₁ : ∀ n m → n ≡ m + 1 → n + 1 ≡ m + 1 + 1
ex-cong₁ n m eq = cong (λ x → x + 1) eq

--
--   ⟪小ネタ⟫
--   λ は \Gl で入力できます。同様に、ギリシャ文字は \G のあとに対応する
--   アルファベットを打つことで入力することができます。また、アルファベットを
--   大文字にするとギリシャ文字も大文字になります。
--
--   例: α (\Ga)、β (\Gb)、γ (\Gg)、ρ (\Gr)、Γ (\GG) など
--

--
-- _+_ などの関数に値を部分適用して関数を作ることもできます。
--

ex-cong₂ : ∀ n m → n ≡ 1 + m → 2 + n ≡ 3 + m
ex-cong₂ n m eq = cong (_+_ 2) eq

--
-- 以下の補題も同様に定義します。
--

sm+n≡m+sn : ∀ m n → suc m + n ≡ m + suc n
sm+n≡m+sn zero    n = refl
sm+n≡m+sn (suc m) n = cong suc (sm+n≡m+sn m n)

--
-- Day1 では +-comm は以下のように証明したと思います。ここで、trans
-- は Day1 での transitivity と同じものです。
--

+-comm : ∀ n m → n + m ≡ m + n
+-comm zero    m = n≡n+0 m
+-comm (suc n) m = trans (cong suc (+-comm n m)) (sm+n≡m+sn m n)

--
--
-- § 2.1. Rewrite パターン
--
--

--
-- rewrite パターン は _≡_ のインスタンスを与えることによって文脈を
-- 書き換えることのできる Agda の機能です。
--
-- たとえば、n について場合分けした状態で、n = suc n のケースのゴールは
-- 次のようになっています。
--
--   +-comm₁ : ∀ n m → n + m ≡ m + n
--   +-comm₁ zero    m = n≡n+0 m
--   +-comm₁ (suc n) m = {!!}0 <-- この穴で C-c C-,
--
--   Goal: suc (n + m) ≡ m + suc n
--   ————————————————————————————————————————————————————————————
--   m : ℕ
--   n : ℕ
--
-- rewrite パターンは次のように、全ての引数より後ろ、= より前に _≡_ の
-- インスタンスを伴って記述します。
--
--   +-comm₁ : ∀ n m → n + m ≡ m + n
--   +-comm₁ zero    m = n≡n+0 m
--   +-comm₁ (suc n) m rewrite +-comm₁ n m = {!!} <-- この穴で C-c C-,
--                             ^^^^^^^^^^^
--
-- ここで、+-comm₁ n m の命題は n + m ≡ m + n です。これにより、文脈中の
-- n + m がすべて m + n に置き換わります。
--
--   Goal: suc (m + n) ≡ m + suc n
--              ^^^^^
--   ————————————————————————————————————————————————————————————
--   m : ℕ
--   n : ℕ
--
-- さらに別の _≡_ のインスタンスで置き換えたい場合は、| で区切って続けて
-- 記述します。
--
--   +-comm₁ : ∀ n m → n + m ≡ m + n
--   +-comm₁ zero    m = n≡n+0 m                       この穴でC-c C-,
--   +-comm₁ (suc n) m rewrite +-comm₁ n m | sm+n≡m+sn m n = {!!}
--                                                            ^^
--   Goal: m + suc n ≡ m + suc n
--   ————————————————————————————————————————————————————————————
--   m : ℕ
--   n : ℕ
--
-- ここまでの操作で、証明すべき命題が m + suc n ≡ m + suc n となったので
-- refl によって証明を完了することができます。
--
-- 以上の手順にしたがって +-comm₁ を証明してみてください。
--

+-comm₁ : ∀ n m → n + m ≡ m + n
+-comm₁ zero    m = n≡n+0 m
+-comm₁ (suc n) m rewrite +-comm₁ n m | sm+n≡m+sn m n = refl

--
-- ここでは rewrite によって証明がほぼ完了してしまいましたが、実際には
-- 文脈を少し書き換えるだけという使い方も多いです。また、等しいことの証明
-- に関しては、より宣言的でわかりやすい次の書き方もあります。
--

--
--
-- § 2.2 The combinators of ≡-Reasoning
--
--

--
-- Relational.Binary.PropositionalEquality で定義されている ≡-Reasoning
-- というモジュールは、trans の使用をうまく隠蔽し推論の過程を分かりやすく
-- 書けるようにした begin_、_≡⟨_⟩_、∎ という(主に)3つの combinator を提供
-- しています。
-- これらの記号は
--   ⟨ は \<
--   ∎ は \qed
-- で入力できます。
--

open ≡-Reasoning

--
-- この combinator の使い方に関しては習うより慣れよですが、簡単に文法を説明すると
-- 次の通りです。
--
-- 証明したい命題が A ≡ B であり、途中 C という値を経由して
--
--   trans (A ≡ C の証明) (C ≡ B の証明)
--
-- のように証明する場合、
--
--   begin
--     A
--   ≡⟨ A ≡ C の証明 ⟩
--     C
--   ≡⟨ C ≡ B の証明 ⟩
--     B
--   ∎
--
-- という風に書くことができます。実際に +-comm を証明してみると次のようになります。
--

+-comm₂ : ∀ n m → n + m ≡ m + n
+-comm₂ zero    m = n≡n+0 m
+-comm₂ (suc n) m = begin        -- begin で開始
  suc (n + m)                    -- 証明したい命題 suc n + m ≡ m + suc n の左辺の値
                                 --              ^^^^^^^^^
    ≡⟨ cong suc (+-comm₂ n m) ⟩  -- suc (n + m) ≡ suc (m + n) の証明
  suc (m + n)                    -- 途中の値
    ≡⟨ sm+n≡m+sn m n ⟩           -- suc (m + n) ≡ m + (suc n) の証明
  m + (suc n)                    -- 証明したい命題 suc n + m ≡ m + suc n の左辺の値
                                 --                          ^^^^^^^^^
    ∎                            -- ∎ で終了

--
--   ⟪注意⟫
--   rewrite とは異なり、A ≡⟨ ... ⟩ B のカッコの中に記述する証明は A ≡ B の
--   ``完全''な証明である必要があります。rewrite の場合は cong suc が不要
--   でしたが、≡-Reasoning の combinator を使う場合には cong suc が必要です。
--   よくはまるので注意してください。
--
-- trans を使った証明に比べてすべての値を記述するので冗長ですが、その分宣言的で
-- 分かりやすくなっています。実際には、とりあえず両辺の値を書いた後に間を埋めていく
-- という使い方をすることが多いように思います。
--

--
--
-- § 2.3. SemiringSolver
--
--

--
-- 実は、この程度の命題であれば自動で証明できてしまいます。
--

open import Data.Nat.Properties
open SemiringSolver

+-comm₃ : ∀ n m → n + m ≡ m + n
+-comm₃ = solve 2 (λ n m → n :+ m := m :+ n) refl

--
-- 掛け算も :* で扱うことができます。
--

--
--
-- § 2.4 Exercise
--
--

--
-- 1.
-- +-assoc を rewrite もしくは ≡-Reasoning を使って証明してください。
--

+-assoc : ∀ n m o → n + m + o ≡ n + (m + o)
+-assoc = {!!}

--
-- 2.
-- 掛け算は以下のように定義されます(Data.Nat の定義と重複するのでコメント
-- アウトしています)。
--
--   _*_ : ℕ → ℕ → ℕ
--   zero    * m = zero
--   (suc n) * m = m + n * m
--
-- 掛け算に関するいくつかの性質を証明してください。
--

n*0≡0 : ∀ n → n * zero ≡ zero
n*0≡0 zero    = refl
n*0≡0 (suc n) = n*0≡0 n

n*1≡n : ∀ n → n * 1 ≡ n
n*1≡n zero = refl
n*1≡n (suc n) = cong suc (n*1≡n n)

n*2≡n+n : ∀ n → n * 2 ≡ n + n
n*2≡n+n zero = refl
n*2≡n+n (suc n) rewrite +-comm n (suc n) =
  cong (λ x → suc (suc x)) (n*2≡n+n n)

m*sn≡m+m*n : ∀ m n → m * (suc n) ≡ m + m * n
m*sn≡m+m*n zero n = refl
m*sn≡m+m*n (suc m) n rewrite m*sn≡m+m*n m n = cong suc (begin
  n + (m + m * n)
    ≡⟨ sym (+-assoc n m _) ⟩
  n + m + m * n
    ≡⟨ cong (λ x → x + m * n) (+-comm n m) ⟩
  m + n + m * n
    ≡⟨ +-assoc m n _ ⟩
  m + (n + m * n)
    ∎)

*-comm : ∀ n m → n * m ≡ m * n
*-comm zero m = sym (n*0≡0 m)
*-comm (suc n) m rewrite m*sn≡m+m*n m n = cong (_+_ m) (*-comm n m)

*-distrib-+₁ : ∀ n m o → (n + m) * o ≡ n * o + m * o
*-distrib-+₁ zero m o = refl
*-distrib-+₁ (suc n) m o = begin
  o + (n + m) * o
    ≡⟨ cong (_+_ o) (*-distrib-+₁ n m o) ⟩
  o + (n * o + m * o)
    ≡⟨ sym (+-assoc o (n * o) (m * o)) ⟩
  o + n * o + m * o
    ∎

*-distrib-+₂ : ∀ n m o → n * (m + o) ≡ n * m + n * o
*-distrib-+₂ zero m o = refl
*-distrib-+₂ (suc n) m o = begin
  m + o + n * (m + o)
    ≡⟨ cong (_+_ (m + o)) (*-distrib-+₂ n m o) ⟩
  m + o + (n * m + n * o)
    ≡⟨ +-assoc m o (n * m + n * o) ⟩
  m + (o + (n * m + n * o))
    ≡⟨ cong (_+_ m) (sym (+-assoc o (n * m) _)) ⟩
  m + (o + n * m + n * o)
    ≡⟨ cong (λ x → m + (x + n * o)) (+-comm o (n * m)) ⟩
  m + (n * m + o + n * o)
    ≡⟨ cong (_+_ m) (+-assoc (n * m) o _) ⟩
  m + (n * m + (o + n * o))
    ≡⟨ sym (+-assoc m (n * m) _) ⟩
  m + n * m + (o + n * o)
    ∎

*-distrib-+₂′ : ∀ n m o → n * (m + o) ≡ n * m + n * o
*-distrib-+₂′ n m o rewrite *-comm n (m + o)
                          | *-comm n m
                          | *-comm n o = *-distrib-+₁ m o n

expand : ∀ a b c d → (a + b) * (c + d) ≡ (a * c + b * c) + (a * d + b * d)
expand a b c d = begin
  (a + b) * (c + d)
    ≡⟨ *-distrib-+₂ (a + b) c d ⟩
  (a + b) * c + (a + b) * d
    ≡⟨ cong (λ x → x + (a + b) * d) (*-distrib-+₁ a b c) ⟩
  a * c + b * c + (a + b) * d
    ≡⟨ cong (_+_ (a * c + b * c)) (*-distrib-+₁ a b d) ⟩
  a * c + b * c + (a * d + b * d)
    ∎
