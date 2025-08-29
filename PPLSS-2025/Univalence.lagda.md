# Univalenceの簡約例

Cubical AgdaでUnivalenceが簡約されることを見る。

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
module PPLSS-2025.Univalence where
```

ライブラリのインポート。

```agda
open import Cubical.Foundations.Prelude
  using
  ( Type
  ; _≡_
  ; refl
  ; transport
  )
```

Cubical Agdaの標準ライブラリでは「同型」のなす型`Iso A B`が提供される。
これは`f : A → B`と`g : B → A`と`η : ∀ x → g (f x) ≡ x`と`ε : ∀ y → f (g y)`の組からなる型である。
`Iso A B`と`A ≃ B`は同値**ではない**が関数`Iso A B → A ≃ B`と`A ≃ B → Iso A B`を構成することはできる。
Univalenceと合わせると、`isoToPath : Iso A B → A ≡ B`を構成できる。

```agda
open import Cubical.Foundations.Isomorphism
  using
  ( Iso
  ; isoToPath
  )
```

## Bool型

**Bool型**は真偽値`false`と`true`で生成される。

```agda
data Bool : Type₀ where
  false : Bool
  true : Bool
```

否定演算は真偽値を逆転させる。

```agda
not : Bool → Bool
not x = {!!}
```

否定を2回すると元に戻る。

```agda
not-not : ∀ b → not (not b) ≡ b
not-not x = {!!}
```

否定演算は同型に拡張される。

```agda
not-iso : Iso Bool Bool
Iso.fun not-iso = not
Iso.inv not-iso = not
Iso.rightInv not-iso = not-not
Iso.leftInv not-iso = not-not
```

## Univalence

Univalenceにより、同型から同一視を得る。

```agda
not-path : Bool ≡ Bool
not-path = isoToPath not-iso
```

簡約を確かめる。
`refl`に型`a ≡ b`が付くのは`a`と`b`が同一の項に簡約される時なので、型チェックにより簡約を確かめられる。

```agda
_ : transport not-path true ≡ false
_ = {!!}

_ : transport not-path false ≡ true
_ = {!!}
```

## 補足：変数を含む場合のUnivalenceの簡約

上記の`transport not-path true`が`false`に簡約されたのは、その型が変数を含まないことによる。
型が変数を含む場合にはこれほど分かりやすく簡約されるわけではない。
以下の例では直積の成分を入れ替える同一視`swap-path : (A × B) ≡ (B × A)`を考える。

```agda
open import Cubical.Foundations.Prelude
  using
  ( ℓ-max
  ; transp
  ; i0
  )

data _×_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  _,_ : A → B → A × B

swap : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
  → A × B → B × A
swap (a , b) = b , a

swap-swap : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
  (x : A × B) → swap (swap x) ≡ x
swap-swap (a , b) = refl

swap-iso : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
  → Iso (A × B) (B × A)
Iso.fun swap-iso = swap
Iso.inv swap-iso = swap
Iso.rightInv swap-iso = swap-swap
Iso.leftInv swap-iso = swap-swap

swap-path : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
  → (A × B) ≡ (B × A)
swap-path = isoToPath swap-iso
```

`transport swap-path (a , b)`は`(b , a)`に簡約**されず**、次のコードは型エラーとなる。

```text
_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {a : A} {b : B}
  → transport swap-path (a , b) ≡ (b , a)
_ = refl
```

次のような「標準形」に簡約されることは分かる。

```agda
_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {a : A} {b : B}
  → transport swap-path (a , b) ≡
    (transp (λ _ → B) i0 b , transp (λ _ → A) i0 a)
_ = refl
```

プリミティヴ`transp`が型についての場合分けで定義されるため、`A`と`B`が型変数の場合にはこれ以上簡約できない。
`A`と`B`が変数を含まない型の場合は、さらに簡約される。
次の例は`A = Bool`で`B = Bool × Bool`の場合。

```agda
_ : {x y z : Bool} → transport swap-path (x , (y , z)) ≡ ((y , z) , x)
_ = refl
```
