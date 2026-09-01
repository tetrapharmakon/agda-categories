{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Variants.Slice {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

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

-- THERE IS NO PROFUNCTOR C.op x C -> Sets sending (A , B) to MR2 A B, and this
-- file no longer declares one.
--
-- The obstruction is precise: reindexing the repair datum along
-- (u : A' => A , v : B => B') needs a functor Slice B' -> Slice B, i.e. pullback
-- along v, which this module does not assume; postcomposition with v runs the
-- other way.  A Bifunctor asserting the profunctor's existence, with the missing
-- datum postulated, used to stand here.  It has been removed: the comment above
-- it denied the object exists while the term below it asserted the opposite.
--
-- What survives is what is true and proved: MR2 and MR2-Setoid.  Adding pullback
-- along v to this module's hypotheses is what it would take to build the
-- profunctor for real.
