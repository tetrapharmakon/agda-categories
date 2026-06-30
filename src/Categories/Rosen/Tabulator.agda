{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_; lift)

open import Data.Product using (_,_; proj₁)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import Categories.Functor.Hom using (Hom[_][-,-])

module Categories.Rosen.Tabulator {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C


import Reason
open Reason C


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



ϵ  : NaturalTransformation MRS-Profunctor (LiftSetoids (o ⊔ e) (o ⊔ ℓ) ∘F Hom[ C ][-,-])
ϵ = ntHelper record 
  { η = λ { (A , B) → record 
    { _⟨$⟩_ = λ {⟪ f , ϕ ⟫ → lift f }
    ; cong = λ { {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} eq → lift (proj₁ eq) }
    } }
  ; commute = λ { {(A , B)} {(A' , B')} (u , v) {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} eq →
      lift (∘-resp-≈ʳ (∘-resp-≈ˡ (proj₁ eq))) }
  }