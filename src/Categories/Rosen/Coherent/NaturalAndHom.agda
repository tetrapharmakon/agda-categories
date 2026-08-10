{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Properties using (coherence₃)

module Categories.Rosen.Coherent.NaturalAndHom {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute;[_]-decompose₁;[_]-decompose₂;[_]-merge)
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)
open import Categories.Morphism.Reasoning as MR

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
                unitorʳ.from ∘ (id ⊗₁ α) ∘ unitorˡ.to ≈⟨ {! coherence₃ M  !}  ⟩
                unitorˡ.from ∘ (id ⊗₁ α) ∘ unitorˡ.to ≈⟨ pullˡ C (M .Monoidal.unitorˡ-commute-from) ⟩
                (α ∘ unitorˡ.from) ∘ unitorˡ.to ≈⟨ pullʳ C unitorˡ.isoʳ ⟩
                α ∘ id ≈⟨ identityʳ ⟩ α ∎ ⟩
              α ∎
