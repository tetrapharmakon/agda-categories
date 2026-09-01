{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Properties using (coherence₂)
open import Categories.Category.Monoidal.Utilities using (unitor-coherenceʳ; unitorˡ-naturalIsomorphism)
import Categories.NaturalTransformation.NaturalIsomorphism.Properties as NIProps
open import Level using (_⊔_)

module Categories.Rosen.Coherent.NaturalAndHom {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute;[_]-decompose₁;[_]-decompose₂;[_]-merge)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)

import Reason
open Reason C
open Closed Cl using (adjoint; mate;[-,-];[_,-];[-,_]; [_,_]₀; [_,_]₁;⊗;_⊗₀_;_⊗₁_;_⊗-;-⊗_;unit;unitorˡ;unitorʳ;associator)
open HomReasoning
open MR

p : ∀ {A} → (NaturalTransformation idF ([_,-] A)) → (A ⇒ unit)
p α = let module α = NaturalTransformation α
          ℓ = unitorˡ.to
          α#I = adjoint.Radjunct (α.η unit)
      in α#I ∘ ℓ



ι : ∀ {A} →  (A ⇒ unit) → (NaturalTransformation idF ([_,-] A))
ι ξ = let ρ⁻¹ = unitorʳ.from
      in ntHelper (record
         { η = λ X → [ ξ , id {X} ]₁ ∘ adjoint.Ladjunct ρ⁻¹
         ; commute = λ {X} {Y} f →
             begin ([ ξ , id {Y} ]₁ ∘ adjoint.Ladjunct ρ⁻¹) ∘ f                       ≈⟨ pullʳ C (Equiv.sym adjoint.Ladjunct-comm′) ⟩
                  [ ξ , id {Y} ]₁ ∘ adjoint.Ladjunct (ρ⁻¹ ∘ f ⊗₁ id)                 ≈⟨ refl⟩∘⟨ adjoint.Ladjunct-resp-≈ (M .Monoidal.unitorʳ-commute-from) ⟩
                  [ ξ , id {Y} ]₁ ∘ adjoint.Ladjunct (f ∘ ρ⁻¹)                       ≈⟨ refl⟩∘⟨ Functor.homomorphism ([_,-] unit) ⟩∘⟨refl ⟩
                  [ ξ , id {Y} ]₁ ∘ ([ id , f ]₁ ∘ [ id , ρ⁻¹ ]₁) ∘ adjoint.unit.η _ ≈⟨ refl⟩∘⟨ assoc ⟩
                   [ ξ , id {Y} ]₁ ∘ [ id , f ]₁ ∘ adjoint.Ladjunct ρ⁻¹               ≈⟨ pullˡ C (Equiv.sym [ [-,-] ]-commute) ○ assoc ⟩
                   [ id , f ]₁ ∘ [ ξ , id {X} ]₁ ∘ adjoint.Ladjunct ρ⁻¹               ∎
        })

lem : ∀ {A} (α : A ⇒ unit) → p (ι α) ≈ α
lem α = begin adjoint.Radjunct ([ α , id ]₁ ∘ [ id , unitorʳ.from ]₁ ∘ adjoint.unit.η _) ∘ unitorˡ.to ≈⟨ adjoint.Radjunct-resp-≈ (pullˡ C (Equiv.sym [ [-,-] ]-commute) ○ assoc) ⟩∘⟨refl ⟩
              adjoint.Radjunct ([ id , unitorʳ.from ]₁ ∘ [ α , id ]₁ ∘ adjoint.unit.η _) ∘ unitorˡ.to ≈⟨ adjoint.Radjunct-comm′ ⟩∘⟨refl ⟩
              (unitorʳ.from ∘ adjoint.Radjunct ([ α , id ]₁ ∘ adjoint.unit.η _)) ∘ unitorˡ.to ≈⟨ assoc ⟩
              unitorʳ.from ∘ adjoint.Radjunct ([ α , id ]₁ ∘ adjoint.unit.η _) ∘ unitorˡ.to ≈⟨ refl⟩∘⟨ adjoint.Radjunct-resp-≈ (Equiv.sym (mate.commute₁ α)) ⟩∘⟨refl ⟩
              unitorʳ.from ∘ adjoint.Radjunct ([ id , id ⊗₁ α ]₁ ∘ adjoint.unit.η _) ∘ unitorˡ.to ≈⟨ refl⟩∘⟨ adjoint.RLadjunct≈id ⟩∘⟨refl ⟩
              unitorʳ.from ∘ (id ⊗₁ α) ∘ unitorˡ.to ≈⟨ begin
                unitorʳ.from ∘ (id ⊗₁ α) ∘ unitorˡ.to ≈⟨ Equiv.sym unitors ⟩∘⟨refl ⟩
                unitorˡ.from ∘ (id ⊗₁ α) ∘ unitorˡ.to ≈⟨ pullˡ C (M .Monoidal.unitorˡ-commute-from) ⟩
                (α ∘ unitorˡ.from) ∘ unitorˡ.to ≈⟨ pullʳ C unitorˡ.isoʳ ⟩
                α ∘ id ≈⟨ identityʳ ⟩ α ∎ ⟩
              α ∎
  where
  unitors : M .Monoidal.unitorˡ.from {X = M .Monoidal.unit} ≈ M .Monoidal.unitorʳ.from {X = M .Monoidal.unit}
  unitors = NIProps.push-eq (unitorˡ-naturalIsomorphism M) (begin
    id ⊗₁ unitorˡ.from ≈˘⟨ cancelʳ C associator.isoʳ ⟩
    (id ⊗₁ unitorˡ.from ∘ associator.from) ∘ associator.to ≈⟨ M .Monoidal.triangle ⟩∘⟨refl ⟩
    unitorʳ.from ⊗₁ id ∘ associator.to ≈⟨ unitor-coherenceʳ M ⟩∘⟨refl ⟩
    unitorʳ.from ∘ associator.to ≈˘⟨ coherence₂ M ⟩∘⟨refl ⟩
    (id ⊗₁ unitorʳ.from ∘ associator.from) ∘ associator.to ≈⟨ cancelʳ C associator.isoʳ ⟩
    id ⊗₁ unitorʳ.from ∎)


-- THE REVERSE DIRECTION IS FALSE, and this development proves it false.
--
-- One might hope for ι (p α) ≈ α, i.e. that a natural transformation id ⇒ [A,-]
-- is determined by its component at the monoidal unit.  Naturality gives no way
-- to recover the component at X, and the gap is real, not merely underivable:
-- Coherent/C2Sets.agda REFUTES it.  In the cartesian closed category of C₂-sets
-- with A = unit, the nontrivial central element of C₂ is a natural endomorphism
-- of the identity; it is the identity on the terminal unit but swaps the
-- regular C₂-set, so p discards information ι cannot reconstruct.  See
-- `swap-is-counterexample` there.
--
-- There is accordingly nothing to state here.  A postulate asserting it stood
-- in this file for a while, named to warn the reader; it has been removed,
-- since a refuted statement is better recorded by its refutation than by an
-- assumption of its truth.
