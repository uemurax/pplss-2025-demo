# Coinductive types

Cubical Agdaで余帰納的型の同一視が双模倣で特徴付けられることを見る。

動作環境。

*   Agda version 2.6.4.3
*   Cubical Agda v0.8

## Cubical Agda

cubical modeを使うには`--cubical`オプションを指定する。
余再帰的定義を使うには`--guardedness`オプションを指定する。

```agda
{-# OPTIONS --cubical --guardedness --safe #-}
```

トップレベルモジュールの宣言。

```agda
module PPLSS-2025.Coinductive where
```

ライブラリのインポート。

```agda
open import Cubical.Foundations.Prelude
  using
  ( Type
  ; _≡_
  )
open import Cubical.Foundations.Isomorphism
  using
  ( Iso
  ; isoToPath
  )
```

## ストリーム

**ストリーム**は無限長のリスト。

```agda
record Stream {ℓ} (A : Type ℓ) : Type ℓ where
  coinductive
  field
    head : A
    tail : Stream A

open Stream
```

余再帰的定義の例。

```agda
map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → B) → Stream A → Stream B
head (map f xs) = f (xs .head)
tail (map f xs) = map f (xs .tail)
```

## 双模倣

**双模倣**はストリームの各要素の同一視。

```agda
record _≈_ {ℓ} {A : Type ℓ} (xs ys : Stream A) : Type ℓ where
  coinductive
  field
    ≈head : xs .head ≡ ys .head
    ≈tail : xs .tail ≈ ys .tail

open _≈_
```

`≡`と`≈`が一致することを見る。

```agda
module _ {ℓ} {A : Type ℓ} where

  toPath : ∀ {xs ys : Stream A} → xs ≈ ys → xs ≡ ys
  toPath r = {!!}

  fromPath : ∀ {xs ys : Stream A} → xs ≡ ys → xs ≈ ys
  fromPath p = {!!}

  fromPath-toPath : ∀ {xs ys : Stream A} (r : xs ≈ ys)
    → fromPath (toPath r) ≡ r
  fromPath-toPath r = {!!}

  toPath-fromPath : ∀ {xs ys : Stream A} (p : xs ≡ ys)
    → toPath (fromPath p) ≡ p
  toPath-fromPath = {!!}

  Iso-≡-≈ : ∀ {xs ys : Stream A} → Iso (xs ≡ ys) (xs ≈ ys)
  Iso.fun Iso-≡-≈ = fromPath
  Iso.inv Iso-≡-≈ = toPath
  Iso.rightInv Iso-≡-≈ = fromPath-toPath
  Iso.leftInv Iso-≡-≈ = toPath-fromPath

  ≡-≡-≈ : ∀ {xs ys : Stream A} → (xs ≡ ys) ≡ (xs ≈ ys)
  ≡-≡-≈ = isoToPath Iso-≡-≈
```
