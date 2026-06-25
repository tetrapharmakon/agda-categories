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

module Categories.Rosen.Tabulator {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C


import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)
import Categories.Morphism.Reasoning as MR
open HomReasoning 
open MR
open import Categories.Rosen.Core Cl

open import Categories.Functor.Profunctor.Tabulator

open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

𝕋MRS = Tabulator MRS-Profunctor

π  = projection {p = MRS-Profunctor}
þ  = cell {p = MRS-Profunctor}

-- gives f
V₁ : Functor 𝕋MRS Arr.Arrow
V₁ = record
  { F₀ = λ { ((A , B) ∣ ξ) → record { arr = MR2.f ξ } }
  ; F₁ = λ { {(A , B) ∣ ⟪ f , ϕ ⟫} {(A' , B') ∣ ⟪ g , ϕ' ⟫} (l , r ∥ (eq , eq')) → mor⇒ {dom⇒ = l} {cod⇒ = r} 
    (begin r ∘ f      ≈˘⟨ id-2 ⟩ 
           r ∘ f ∘ id ≈⟨ eq ○ identityˡ ⟩
           g ∘ l      ∎) }
  ; identity = 
      Equiv.refl 
    , Equiv.refl
  ; homomorphism = 
      Equiv.refl 
    , Equiv.refl
  ; F-resp-≈ = λ { x → x }
  }

open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)

ϵ  : NaturalTransformation MRS-Profunctor (LiftSetoids (o ⊔ e) (o ⊔ ℓ) ∘F Hom[ C ][-,-])
ϵ = ntHelper record 
  { η = λ { (A , B) → record 
    { _⟨$⟩_ = λ {⟪ f , ϕ ⟫ → lift f }
    ; cong = λ { {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} eq → lift (proj₁ eq) }
    } }
  ; commute = λ { {(A , B)} {(A' , B')} (u , v) {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} eq →
      lift (∘-resp-≈ʳ (∘-resp-≈ˡ (proj₁ eq))) }
  }