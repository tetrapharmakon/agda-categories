{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

-- open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Rosen.Incoherent.Functors {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —Φ→ [A,B]
-- without the natural transformation condition of full MR2.

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor;_∘F_)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute;[_]-decompose₁;[_]-decompose₂)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using (adjoint; mate;[-,-]; [_,_]₀; [_,_]₁;⊗;_⊗₀_;_⊗₁_;_⊗-;-⊗_)
open HomReasoning
open MR

-- open Symmetric S hiding (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_) renaming (braided-iso to β)
-- module Arr = Categories.Category.Construction.Arrow C

open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Elements Cl

module _ {X Y : iMR2₀} (f : twiMR2⇒ X Y) where
  module X = iMR2₀ X
  module Y = iMR2₀ Y
  module F = twiMR2⇒ f

  lemma-epsilon :
    F.r ∘ adjoint.counit.η X.B ∘ id ⊗₁ F.l ≈
    adjoint.counit.η Y.B ∘ [ F.l , F.r ]₁ ⊗₁ id
  lemma-epsilon = {!   !}

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

Arbib : Functor τ'[iMR2] totalMealy
Arbib = record
  { F₀ = λ x → 
    let module x = iMR2₀ x 
        module ξX = iMR2 x.ξ
        Φ* = adjoint.Radjunct ξX.Φ
    in record 
    { A = x.A 
    ; B = x.B 
    ; m = record 
      { E = [ x.A , x.B ]₀ 
      ; d = adjoint.Ladjunct (Φ* ∘ (adjoint.counit.η x.B ⊗₁ id)) 
      ; s = adjoint.counit.η x.B 
      } 
    }
  ; F₁ = λ f → 
    let module f = twiMR2⇒ f 
        module AX = adjoint {f.X.A}
        module AY = adjoint {f.Y.A}
        εXB = AX.counit.η f.X.B
        εYB = AY.counit.η f.Y.B
    in record 
      { l = f.l
      ; r = f.r 
      ; u = [ f.l , f.r ]₁ 
      ; d-eq = {!  !} 
      ; s-eq = lemma-epsilon f 
      }
  ; identity = refl , refl , [-,-].identity
  ; homomorphism = refl , refl , [-,-].homomorphism
  ; F-resp-≈ = λ z → z .proj₁ , z .proj₁ , [-,-].F-resp-≈ z
  }
