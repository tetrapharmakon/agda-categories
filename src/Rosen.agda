{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)

open import Data.Product using (_,_; proj₂; _×_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.NaturalTransformation using (NaturalTransformation;_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

module Rosen {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁)

module Arr = Categories.Category.Construction.Arrow C

-- Codomain functor Arrow(C) → C.
Cod : Functor Arr.Arrow C
Cod = record
  { F₀           = Arr.Morphism.cod
  ; F₁           = Arr.Morphism⇒.cod⇒
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → proj₂ eq
  }

record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    ϕ : NaturalTransformation Cod (([_,-] A) ∘F Cod)

MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) e
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ p q → (MR2.f p ≈ MR2.f q) × (MR2.ϕ p ≃ MR2.ϕ q)
  ; isEquivalence = record
    { refl  = Equiv.refl , IsEquivalence.refl  ≃-isEquivalence
    ; sym   = λ (pf , pϕ) → Equiv.sym pf , IsEquivalence.sym ≃-isEquivalence pϕ
    ; trans = λ (pf₁ , pϕ₁) (pf₂ , pϕ₂) → Equiv.trans pf₁ pf₂ , IsEquivalence.trans ≃-isEquivalence pϕ₁ pϕ₂
    }
  }


nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record 
  { η = λ X → [ f , id ]₁ 
  ; commute = λ h → Equiv.sym ([ [-,-] ]-commute {f = f} {g = h})
  ; sym-commute = λ h → [ [-,-] ]-commute {f = f} {g = h}
  }



import Categories.Morphism.Reasoning as MR

open HomReasoning 
-- Type of the desired profunctor C.op × C → Sets sending (A , B) ↦ MR2 A B.
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) _)
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record 
    { _⟨$⟩_ = λ {⟪ f , ϕ ⟫ → ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ ϕ ⟫ }
    ; cong = λ { {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} (f≈g , ϕ≈ϕ') →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , (λ {x} → ∘-resp-≈ʳ (ϕ≈ϕ' {x}))
      }
    }}
  ; identity = λ { {(A , B)} {⟪ f , ϕ ⟫} →
      let module Hom = Functor [-,-] in
      let module CodF = Functor Cod in
      (begin
        id ∘ f ∘ id ≈⟨ ∘-resp-≈ Equiv.refl identityʳ ⟩
        id ∘ f      ≈⟨ identityˡ ⟩
        f           ∎)
    , (λ {x} →
        begin
          [ id , id ]₁ ∘ NaturalTransformation.η ϕ x
            ≈⟨ ∘-resp-≈ˡ (Hom.identity {A = (A , CodF.F₀ x)}) ⟩
          id ∘ NaturalTransformation.η ϕ x
            ≈⟨ identityˡ ⟩
          NaturalTransformation.η ϕ x
        ∎)
    }
  ; homomorphism = λ { {(A , B)} {(A' , B')} {(A'' , B'')} {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , ϕ ⟫} →
      let module Hom = Functor [-,-] in
      (begin
        (v₂ ∘ v₁) ∘ f ∘ (u₁ ∘ u₂)
          ≈⟨ sym-assoc ⟩
        ((v₂ ∘ v₁) ∘ f) ∘ (u₁ ∘ u₂)
          ≈⟨ ∘-resp-≈ assoc Equiv.refl ⟩
        (v₂ ∘ (v₁ ∘ f)) ∘ (u₁ ∘ u₂)
          ≈⟨ assoc ⟩
        v₂ ∘ ((v₁ ∘ f) ∘ (u₁ ∘ u₂))
          ≈⟨ ∘-resp-≈ Equiv.refl sym-assoc ⟩
        v₂ ∘ (((v₁ ∘ f) ∘ u₁) ∘ u₂)
          ≈⟨ ∘-resp-≈ Equiv.refl (∘-resp-≈ assoc Equiv.refl) ⟩
        v₂ ∘ ((v₁ ∘ f ∘ u₁) ∘ u₂)
          ≈⟨ assoc ⟩
        v₂ ∘ (v₁ ∘ f ∘ u₁) ∘ u₂
        ∎)
    , (λ {x} →
        begin
          [ u₁ ∘ u₂ , id ]₁ ∘ NaturalTransformation.η ϕ x
            ≈⟨ ∘-resp-≈ˡ Hom.homomorphism ⟩
          ([ u₂ , id ]₁ ∘ [ u₁ , id ]₁) ∘ NaturalTransformation.η ϕ x
            ≈⟨ assoc ⟩
          [ u₂ , id ]₁ ∘ ([ u₁ , id ]₁ ∘ NaturalTransformation.η ϕ x)
          ∎)
    }
  ; F-resp-≈ = λ { {(A , B)} {(A' , B')} {f = (u , v)} {g = (u' , v')} (u≈u' , v≈v') {⟪ f , ϕ ⟫} →
      let module Hom = Functor [-,-] in
      (∘-resp-≈ v≈v' (∘-resp-≈ Equiv.refl u≈u'))
    , (λ {x} →
        ∘-resp-≈ˡ (Hom.F-resp-≈ (u≈u' , Equiv.refl)))
    }
  }
