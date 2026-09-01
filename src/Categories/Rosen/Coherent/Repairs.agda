{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Coherent.Repairs {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Intuitively, a repair system remembers only the repair component Φ of an
-- (M,R)-system, dropping the metabolic map f.
--
-- The "fibration of repairs": the category of elements of the functor
-- A ↦ Nat(id, [A,-]).  Objects rep₀ are (A, Φ) with Φ : id ⇒ [A,-];
-- morphisms rep⇒ are commuting pairs.  Exports rep₀, rep⇒, repairs.
--
-- Migrated from cod-coherent to id-coherent repair data; see
-- Coherent/CodCoherentEqualIdCoherent.agda for why the two agree.

open import Data.Product using (_,_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.Rosen.Coherent.IdCore Cl

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)
open HomReasoning
open MR

-- Objects of the repair fibration: an object A and a natural transformation Φ : id ⇒ [A,-].
record rep₀ : Set (o ⊔ ℓ ⊔ e) where
  field
    A : Obj
    Φ : NaturalTransformation idF ([_,-] A)


-- Morphisms of the repair fibration: u : X.A ⇒ Y.A such that nHom u ∘ᵥ Y.Φ ≃ X.Φ.
record rep⇒ (X Y : rep₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = rep₀ X
  module Y = rep₀ Y
  field
    u : X.A ⇒ Y.A
    eq : nHom u ∘ᵥ Y.Φ ≃ X.Φ

-- The category of repairs: the total category of the fibration.
repairs : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
repairs = record
  { Obj = rep₀
  ; _⇒_ = λ s t → rep⇒ s t
  ; _≈_ = λ f g →
    let module f = rep⇒ f
        module g = rep⇒ g
    in f.u ≈ g.u
  ; id = record { u = id
       ; eq = cancel (Functor.identity [-,-]) }
  ; _∘_ = λ f g →
    let module f = rep⇒ f
        module g = rep⇒ g
    in record { u = f.u ∘ g.u
         ; eq = λ {x} → (Functor.homomorphism [-, _ ] ⟩∘⟨refl) ∙ assoc ∙ (refl⟩∘⟨ f.eq) ∙ g.eq }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
