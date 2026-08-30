{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Variants.Slice {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  postulate
    sorry : ∀ {u} {A : Set u} → A

-- Core definitions for the category of (M,R)-systems.
-- Exports: Cod, nHom, nHom-identity, MR2, MR2-Setoid, MRS-Profunctor.

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Slice C
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C
open HomReasoning

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)

-- nHom sends f : A ⇒ B to the induced natural transformation [-,f] : [B,-] ⇒ [A,-].
nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record
  { η = λ X → [ f , id ]₁
  ; commute = λ h → Equiv.sym [ [-,-] ]-commute
  ; sym-commute = λ h → [ [-,-] ]-commute
  }

-- nHom-identity: nHom respects identity.
nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
nHom-identity = [-,-].identity

-- definition of an (M,R)-system according to Rosen
record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    Φ : NaturalTransformation (Dom B) (([_,-] A) ∘F (Dom B))

  Φη = NaturalTransformation.η Φ
  Φη₀ = Φη (record { arr = f })
  Φcommute = λ {X Y : Category.Obj (Slice B)} t → NaturalTransformation.commute Φ {X} {Y} t

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal
-- and their Φ components are ≃-equal.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) e
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , Φ ⟫) (⟪ g , Φ′ ⟫) → (f ≈ g)
  ; isEquivalence = record
    { refl = Equiv.refl
    ; sym = λ pf → Equiv.sym pf
    ; trans = λ pf₁ pf₂ → Equiv.trans pf₁ pf₂
    }
  }

open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism;niHelper; _ⓘˡ_; _ⓘʳ_)

-- There is no profunctor C.op × C → Sets
-- sending (A , B) ↦ MR2 A B.
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) e)
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A′ , B′)} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , Φ ⟫ → ⟪ v ∘ f ∘ u , sorry ⟫ }
    ; cong = λ { {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} f≈g →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      }
    }}
  ; identity = λ x → trans identityˡ (trans identityʳ x)
  ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} f≈g →
      begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
            (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
            (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
            (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
            v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎ }
  ; F-resp-≈ = λ x x₁ → ∘-resp-≈ (x .proj₂) (∘-resp-≈ x₁ (x .proj₁))
  }
