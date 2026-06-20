{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.NaturalTransformation using (NaturalTransformation;_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,_])
module Categories.Rosen.FibreA {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

import Categories.Morphism.Reasoning as MR
open HomReasoning 
open MR

open import Categories.Rosen.Core Cl

