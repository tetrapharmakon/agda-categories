{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.Functors {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —Φ→ [A,B]
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

[_]f : Functor τ[iMR2] Arr.Arrow 
[_]f = record
  { F₀ = λ x → let module x = iMR2₀ x in record { dom = x.A ; cod = x.B ; arr = iMR2.f x.ξ }
  ; F₁ = λ f → let module f = iMR2⇒ f in mor⇒ f.eqf
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x
  }

open import Categories.Rosen.Incoherent.Repairs Cl

[_]Φ : Functor τ[iMR2] irepairs
[_]Φ = record
  { F₀ = λ x → let module x = iMR2₀ x in record 
    { A = x.A 
    ; B = x.B 
    ; Φ = iMR2.Φ x.ξ 
    }
  ; F₁ = λ f → let module f = iMR2⇒ f in record 
    { u = f.l
    ; v = f.r
    ; eq = f.eqΦ
    }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ z → z .proj₁
  }


open import Categories.Rosen.Incoherent.Mealy Cl

Arbib : Functor τ[iMR2] totalMealy
Arbib = {!   !}