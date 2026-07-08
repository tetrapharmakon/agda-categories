{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Repairs {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- The "fibration of repairs": the category of elements of the functor
-- A ↦ Nat(Cod, [A,-]∘Cod).  Objects rep₀ are (A, ϕ) with ϕ : Cod ⇒ [A,-]∘Cod;
-- morphisms rep⇒ are commuting pairs.  Exports rep₀, rep⇒, repairs.

open import Data.Product using (_,_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.Rosen.Core Cl

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)
open HomReasoning
open MR

-- Objects of the repair fibration: an object A and a natural transformation ϕ : Cod ⇒ [A,-]∘Cod.
record rep₀ : Set (o ⊔ ℓ ⊔ e) where
  field
    A : Obj
    ϕ : NaturalTransformation Cod (([_,-] A) ∘F Cod)

-- Morphisms of the repair fibration: u : X.A ⇒ Y.A such that
-- (nHom u ∘ʳ Cod) ∘ᵥ Y.ϕ ≃ X.ϕ.
record rep⇒ (X Y : rep₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = rep₀ X
  module Y = rep₀ Y
  field
    u : X.A ⇒ Y.A
    eq : (nHom u ∘ʳ Cod) ∘ᵥ Y.ϕ ≃ X.ϕ

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
