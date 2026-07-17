{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.Iterated {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —ϕ→ [A,B]
-- without the natural transformation condition of full MR2.

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₀; [_,_]₁)
open HomReasoning
open MR

-- module Arr = Categories.Category.Construction.Arrow C

open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Functors Cl


{-
This implementation of the span composition 

 ↙ iMRS  ↘  ↙ iMRS  ↘
C         C          C

is simpler than the isoComma object.

here I want to define a category iMRSᴵᴵ having:

for objects iMRSᴵᴵ₀ a record containing as fields 
- an iMRS A B
- an iMRS B Y

for morphisms the "obvious" thing

-}

record iMRSᴵᴵ₀ : Set (o ⊔ ℓ) where
  field
    A B Y : Obj
    ξ₁ : iMR2 A B
    ξ₂ : iMR2 B Y
  hor : iMR2₀
  hor = record { A = A ; B = B ; ξ = ξ₁ }

  vert : iMR2₀
  vert = record { A = B ; B = Y ; ξ = ξ₂ }

record iMRSᴵᴵ⇒ (S T : iMRSᴵᴵ₀) : Set (o ⊔ ℓ ⊔ e) where
  module S = iMRSᴵᴵ₀ S
  module T = iMRSᴵᴵ₀ T
  field
    h : iMR2⇒ S.hor T.hor
    k : iMR2⇒ S.vert T.vert
  module h = iMR2⇒ h
  module k = iMR2⇒ k
  field
    hᵣ≈kₗ : h.r ≈ k.l


iMRSᴵᴵ : Category _ _ _
iMRSᴵᴵ = record
  { Obj = iMRSᴵᴵ₀
  ; _⇒_ = λ s t → iMRSᴵᴵ⇒ s t
  ; _≈_ = λ p q → {!   !}
  ; id = {!   !}
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }