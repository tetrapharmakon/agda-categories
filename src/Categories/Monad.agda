{-# OPTIONS --without-K --safe #-}
module Categories.Monad {o ℓ e} where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

record Monad (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    η : NaturalTransformation idF F
    μ : NaturalTransformation (F ∘F F) F

  module F = Functor F
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

  open Category C
  open F

  field
    assoc     : ∀ {X : Obj} → μ.η X ∘ F₁ (μ.η X) ≈ μ.η X ∘ μ.η (F₀ X)
    sym-assoc : ∀ {X : Obj} → μ.η X ∘ μ.η (F₀ X) ≈ μ.η X ∘ F₁ (μ.η X)
    identityˡ : ∀ {X : Obj} → μ.η X ∘ F₁ (η.η X) ≈ id
    identityʳ : ∀ {X : Obj} → μ.η X ∘ η.η (F₀ X) ≈ id

module _ (C : Category o ℓ e) where
  open Monad
  open Category C hiding (id)
  id : Monad C
  id .F = idF
  id .η = idN
  id .μ = unitor² .F⇒G
  id .assoc = Equiv.refl
  id .sym-assoc = Equiv.refl
  id .identityˡ = identity²
  id .identityʳ = identity²


record monadMap {C : Category o ℓ e} (S : Monad C) (T : Monad C) : Set (o ⊔ ℓ ⊔ e) where 
  field
    α : NaturalTransformation (Monad.F S) (Monad.F T)
  
  module α = NaturalTransformation α
  module S = Monad.F S
  module T = Monad.F T
  
  open Category C
  open S 
  open T
  open α 

  field
    resp-id : ∀ {X : Obj} → Monad.η.η T X ≈ α.η X ∘ Monad.η.η S X
    resp-mu : ∀ {X : Obj} → α.η X ∘ Monad.μ.η S X ≈ (Monad.μ.η T X ∘ NaturalTransformation.η (α ∘ₕ α) X)