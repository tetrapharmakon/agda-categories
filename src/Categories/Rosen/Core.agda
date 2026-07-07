{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Data.Product using (_,_; proj₁; proj₂; _×_)
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
open import Categories.NaturalTransformation.Equivalence using (_≃_)

module Categories.Rosen.Core {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Core definitions for the category of (M,R)-systems.
-- Exports: Cod, nHom, nHom-identity, MR2, MR2-Setoid, MRS-Profunctor.

private
  module 𝒞 = Category C

import Reason
open Reason C

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)

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

-- nHom sends f : A ⇒ B to the induced natural transformation [-,f] : [B,-] ⇒ [A,-].
nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record
  { η = λ X → [ f , id ]₁
  ; commute = λ h → Equiv.sym [ [-,-] ]-commute
  ; sym-commute = λ h → [ [-,-] ]-commute
  }

open import Categories.NaturalTransformation renaming (id to idN)

-- nHom-identity: nHom respects identity.
nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
nHom-identity = [-,-].identity

-- definition of an (M,R)-system according to Rosen
record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    ϕ : NaturalTransformation Cod (([_,-] A) ∘F Cod)

  ϕη = NaturalTransformation.η ϕ
  ϕη₀ = ϕη (record { arr = f })
  ϕcommute = λ {X Y : Category.Obj Arr.Arrow} t → NaturalTransformation.commute ϕ {X} {Y} t

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal
-- and their ϕ components are ≃-equal.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , ϕ ⟫) (⟪ g , ϕ' ⟫) → (f ≈ g) × (ϕ ≃ ϕ')
  ; isEquivalence = record
    { refl = Equiv.refl , (λ {x₁} → Equiv.refl)
    ; sym = λ (pf , k) → Equiv.sym pf , Equiv.sym k
    ; trans = λ (pf₁ , h) (pf₂ , k) → Equiv.trans pf₁ pf₂ , Equiv.trans h k
    }
  }

import Categories.Morphism.Reasoning as MR

open HomReasoning
open MR

-- Type of the desired profunctor C.op × C → Sets 
-- sending (A , B) ↦ MR2 A B.
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , ϕ ⟫ → ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ ϕ ⟫ }
    ; cong = λ { {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} (f≈g , ϕ≈ϕ') →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , (λ {x} → ∘-resp-≈ʳ (ϕ≈ϕ' {x}))
      }
    }}
  ; identity = λ { {(A , B)} {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} →
      let module Hom = Functor [-,-] in
      let module CodF = Functor Cod in
        ( λ (f≈g , ϕ≈ϕ') → Equiv.trans identityˡʳ f≈g
        , λ { {h} → Equiv.trans (elimˡ C Hom.identity) (ϕ≈ϕ' {h}) })
     }
  ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} →
       let module Hom = Functor [-,-]
           module Hom[1-] {A} = Functor (appˡ [-,-] A)
           module Hom[-1] {A} = Functor (appʳ [-,-] A) in
         ( λ { (f≈g , ϕ≈ϕ') →
             (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
                    (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
                    (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
                    (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
                    v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
        , λ { {h} →
            let module ϕ = NaturalTransformation ϕ
                module ϕ' = NaturalTransformation ϕ'
            in
            begin [ u₁ ∘ u₂ , id ]₁ ∘ ϕ.η h              ≈⟨ ∘-resp-≈ Equiv.refl (ϕ≈ϕ' {h}) ⟩
                  [ u₁ ∘ u₂ , id ]₁ ∘ ϕ'.η h             ≈⟨ Hom[-1].homomorphism ⟩∘⟨refl ⟩
                  ([ u₂ , id ]₁ ∘ [ u₁ , id ]₁) ∘ ϕ'.η h ≈⟨ assoc ⟩
                  [ u₂ , id ]₁ ∘ ([ u₁ , id ]₁ ∘ ϕ'.η h) ∎ } })
     }
  ; F-resp-≈ = λ { {(A , B)} {(A' , B')} {f = (u , v)} {g = (u' , v')} (u≈u' , v≈v') {⟪ f , ϕ ⟫} {⟪ g , ϕ' ⟫} →
       let module Hom = Functor [-,-] in
         ( λ { (f≈g , ϕ≈ϕ') → ∘-resp-≈ v≈v' (∘-resp-≈ f≈g u≈u')
        , λ { {h} →
            let module ϕ = NaturalTransformation ϕ
                module ϕ' = NaturalTransformation ϕ'
            in ∘-resp-≈ (Hom.F-resp-≈ (u≈u' , Equiv.refl)) (ϕ≈ϕ' {h})
              } })
     }
  }