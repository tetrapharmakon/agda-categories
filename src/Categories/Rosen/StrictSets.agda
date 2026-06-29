{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (_,_; proj₁; proj₂; _×_;Σ)
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
module Categories.Rosen.StrictSets {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

-- open 𝒞

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

-- import Categories.Morphism.Reasoning as MR
-- open HomReasoning 
-- open MR

import Reason
open Reason C

open import Categories.Rosen.Core Cl
open import Categories.Functor.Profunctor.Tabulator

-- open import Categories.Category.Instance.Sets

{-
MRS-SetP : Bifunctor (Category.op C) C (Sets (o ⊔ ℓ ⊔ e))
MRS-SetP = record
  { F₀ = λ {(A , B) → MR2 A B}
  ; F₁ = λ { {(A , B)} {(A' , B')} (u , v) ⟪ f , ϕ ⟫ → let module ϕ = NaturalTransformation ϕ in
    ⟪ v ∘ f ∘ u , (nHom u ∘ʳ Cod) ∘ᵥ ϕ ⟫}
  ; identity = λ { {(X , Y)} {⟪ f , phi ⟫} →  {! identityˡʳ !}}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }
-}
-- open import Categories.Category.Construction.Elements using (Elements)

-- a modified category of elements definition

Elts : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)) → Category ? ? ?
Elts F = record
  { Obj       = ? -- Σ (Obj × Obj) F₀
  ; _⇒_       = ? -- λ { (c , x) (c′ , x′) → Σ (c ⇒ c′) (λ f → F₁ f x ≡ x′)  }
  ; _≈_       = ? -- λ p q → proj₁ p ≈ proj₁ q
  ; id        = ? -- id , identity
  ; _∘_       = ? -- λ { (f , Ff≡) (g , Fg≡) → f ∘ g ,  trans homomorphism (trans (cong (F₁ f) Fg≡) Ff≡)}
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈  = ∘-resp-≈
  } where open Functor F

𝓔MRS = ? --  Elements MRS-SetP

import Categories.Morphism.Reasoning as MR