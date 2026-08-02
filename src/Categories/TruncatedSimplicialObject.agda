{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.TruncatedSimplicialObject {o ℓ e} (C : Category o ℓ e) where

open import Level

open Category C

record TruncatedSimplicialObject : Set (o ⊔ ℓ ⊔ e) where
  field
    X₀ X₁ X₂ : Obj

    d₀¹ d₁¹ : X₁ ⇒ X₀
    d₀² d₁² d₂² : X₂ ⇒ X₁

    s₀⁰ : X₀ ⇒ X₁
    s₀¹ s₁¹ : X₁ ⇒ X₂

    d₀¹-s₀⁰ : d₀¹ ∘ s₀⁰ ≈ id
    d₁¹-s₀⁰ : d₁¹ ∘ s₀⁰ ≈ id

    face-face₀₁ : d₀¹ ∘ d₁² ≈ d₀¹ ∘ d₀²
    face-face₀₂ : d₀¹ ∘ d₂² ≈ d₁¹ ∘ d₀²
    face-face₁₂ : d₁¹ ∘ d₂² ≈ d₁¹ ∘ d₁²

    degen-degen₀₀ : s₀¹ ∘ s₀⁰ ≈ s₁¹ ∘ s₀⁰

    d₀²-s₀¹ : d₀² ∘ s₀¹ ≈ id
    d₁²-s₀¹ : d₁² ∘ s₀¹ ≈ id
    d₁²-s₁¹ : d₁² ∘ s₁¹ ≈ id
    d₂²-s₁¹ : d₂² ∘ s₁¹ ≈ id
    face-degen₀₁ : d₀² ∘ s₁¹ ≈ s₀⁰ ∘ d₀¹
    face-degen₂₀ : d₂² ∘ s₀¹ ≈ s₀⁰ ∘ d₁¹

open TruncatedSimplicialObject public
