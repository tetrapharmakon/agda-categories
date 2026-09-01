{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category

module Categories.Rosen.TruncatedSemisimplicialObject {o ℓ e} (C : Category o ℓ e) where

-- Two weakenings of Categories.TruncatedSimplicialObject.
--
-- Neither is specific to (M,R)-systems and both would sit more naturally
-- upstream; they live here because agda-categories is outside the perimeter of
-- this development.
--
-- WHY THEY EXIST.  The iterated incoherent (M,R)-systems do not form a
-- truncated simplicial object: exactly one of the thirteen identities fails,
-- namely d₁² ∘ s₀¹ ≈ id, and it fails for a reason (see
-- Incoherent/IteratedTruncatedSemisimplicialObject.agda).  Asserting the full
-- structure and postulating that one identity, which is what this development
-- used to do, states something false.  The honest statements are the two below:
--
--   * TruncatedSemisimplicialObject drops the degeneracies altogether and keeps
--     only the faces and their three identities.  This is the structure the
--     paper claims, and it holds outright.
--
--   * AlmostTruncatedSimplicialObject keeps everything the full record has
--     EXCEPT the single field d₁²-s₀¹.  Constructing it is what turns "only one
--     identity breaks" from a remark into a machine-checked statement: the
--     other twelve are all there.
--
-- The second is not a standard notion and is not meant to be one.  It is a
-- measurement of how far the construction falls short.

open import Level using (_⊔_)

open Category C

-- Faces only.  This is a semisimplicial object, truncated at level 2.
record TruncatedSemisimplicialObject : Set (o ⊔ ℓ ⊔ e) where
  field
    X₀ X₁ X₂ : Obj

    d₀¹ d₁¹ : X₁ ⇒ X₀
    d₀² d₁² d₂² : X₂ ⇒ X₁

    face-face₀₁ : d₀¹ ∘ d₁² ≈ d₀¹ ∘ d₀²
    face-face₀₂ : d₀¹ ∘ d₂² ≈ d₁¹ ∘ d₀²
    face-face₁₂ : d₁¹ ∘ d₂² ≈ d₁¹ ∘ d₁²

-- Everything a TruncatedSimplicialObject has, minus the single identity
--
--     d₁²-s₀¹ : d₁² ∘ s₀¹ ≈ id
--
-- and nothing else.  Compare Categories.TruncatedSimplicialObject field by
-- field: the twelve below are exactly its remaining laws.
record AlmostTruncatedSimplicialObject : Set (o ⊔ ℓ ⊔ e) where
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
    -- d₁²-s₀¹ : d₁² ∘ s₀¹ ≈ id      -- deliberately absent
    d₁²-s₁¹ : d₁² ∘ s₁¹ ≈ id
    d₂²-s₁¹ : d₂² ∘ s₁¹ ≈ id
    face-degen₀₁ : d₀² ∘ s₁¹ ≈ s₀⁰ ∘ d₀¹
    face-degen₂₀ : d₂² ∘ s₀¹ ≈ s₀⁰ ∘ d₁¹

open TruncatedSemisimplicialObject public
open AlmostTruncatedSimplicialObject public
