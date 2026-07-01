{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ʳ_) renaming (NaturalTransformation to NT)
open import Categories.Adjoint using (_⊣_)

module Categories.Rosen.FibredFunctors {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

import Categories.Morphism.Reasoning as MR
open HomReasoning
open MR

open import Categories.Rosen.Core Cl
open import Categories.Rosen.TotalCategory Cl using (tot⇒; total; [_,_∥_,_])
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}

open import Categories.Functor.Profunctor.Tabulator

open import Categories.Rosen.Tabulator Cl using (V₁;𝕋MRS)

module _ (A : Obj) where
  private
    module El = Category ElMRS
    module TM = Category 𝕋MRS
    module Ar = Category Arr.Arrow
    module F  = Functor ℝ
    module G  = Functor V₁

  import Categories.Morphism as M using (_≅_)
  open M Arr.Arrow using (_≅_)
  record psdPB₀ : Set (o ⊔ ℓ ⊔ e) where
    field
      x   : El.Obj
      y   : TM.Obj
      iso : (F.F₀ x) ≅ (G.F₀ y)

  record psdPB⇒ (P Q : psdPB₀) : Set (o ⊔ ℓ ⊔ e) where
    module P = psdPB₀ P
    module Q = psdPB₀ Q
    module iP = _≅_ P.iso
    module iQ = _≅_ Q.iso
    field
      f : El._⇒_ P.x Q.x
      g : TM._⇒_ P.y Q.y
      commute : G.F₁ g Ar.∘ iP.from Ar.≈ iQ.from Ar.∘ F.F₁ f

  MRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
  MRS3 = record
    { Obj = psdPB₀
    ; _⇒_ = psdPB⇒
    ; _≈_ = λ { u v → psdPB⇒.f u El.≈ psdPB⇒.f v × psdPB⇒.g u TM.≈ psdPB⇒.g v }
    ; id = λ { {P} →
        let module P = psdPB₀ P
            module iP = _≅_ P.iso
            d = iP.from .Arr.Morphism⇒.dom⇒
            c = iP.from .Arr.Morphism⇒.cod⇒
        in record 
        { f = El.id 
        ; g = TM.id 
        ; commute = id-comm-sym C {f = d}
          , Equiv.trans (id-comm-sym C {f = c})
                        (Equiv.sym (refl⟩∘⟨ ([-,-].identity)))
        } }
    ; _∘_ = λ { {P} {Q} {R} u v →
        let module P  = psdPB₀ P
            module Q  = psdPB₀ Q
            module R  = psdPB₀ R
            module u  = psdPB⇒ u
            module v  = psdPB⇒ v
            module iP = _≅_ P.iso
            module iQ = _≅_ Q.iso
            module iR = _≅_ R.iso
            p₀ = iP.from .Arr.Morphism⇒.dom⇒
            p₁ = iP.from .Arr.Morphism⇒.cod⇒
            q₀ = iQ.from .Arr.Morphism⇒.dom⇒
            q₁ = iQ.from .Arr.Morphism⇒.cod⇒
            r₀ = iR.from .Arr.Morphism⇒.dom⇒
            r₁ = iR.from .Arr.Morphism⇒.cod⇒
        in record 
        { f = u.f El.∘ v.f
        ; g = u.g TM.∘ v.g
        ; commute = (proj₁ {!  !} ⟩∘⟨refl ○ assoc 
                  ○ refl⟩∘⟨ proj₁ v.commute ○ sym-assoc 
                  ○ proj₁ u.commute ⟩∘⟨refl ○ assoc)
                  , (proj₂ {!  !} ⟩∘⟨refl ○ assoc 
                  ○ refl⟩∘⟨ proj₂ v.commute ○ sym-assoc 
                  ○ proj₂ u.commute ⟩∘⟨refl ○ assoc 
                  ○ refl⟩∘⟨ Equiv.sym (proj₂ {!  !}))
              } }
    ; assoc     = {!  !}
    ; sym-assoc = {! sym-assoc !}
    ; identityˡ = {! identityˡ !}
    ; identityʳ = {! identityʳ !}
    ; identity² = {! identity² !}
    ; equiv = {!  !}
    ; ∘-resp-≈ = {!  !}
    }