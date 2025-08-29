# HITの例

Cubical AgdaでHITに触れる。

動作環境。

*   Agda version 2.6.4.3
*   Cubical Agda v0.8

## Cubical Agda

cubical modeを使うには`--cubical`オプションを指定する。

```agda
{-# OPTIONS --cubical --safe #-}
```

トップレベルモジュールの宣言。

```agda
module PPLSS-2025.HIT where
```

ライブラリのインポート。

```agda
open import Cubical.Foundations.Prelude
  using
  ( Type
  ; _≡_
  ; _∙_
  ; cong
  ; refl
  )
```

## 円周

**円周**または**1次元球面**は基点とその上のループで生成される。

```agda
data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base
```

ループを2周する関数。

```agda
double : S¹ → S¹
double x = {!!}
```

計算例。

```agda
_ : double base ≡ base
_ = {!!}

_ : cong double loop ≡ loop ∙ loop
_ = {!!}
```
