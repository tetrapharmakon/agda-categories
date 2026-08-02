{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (0ℓ; _⊔_;Lift)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor;_∘F_)

module Categories.Rosen.Incoherent.IteratedTruncatedSimplicialObject
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Lift using (liftC;liftF)
open import Categories.TruncatedSimplicialObject using (TruncatedSimplicialObject)

open import Categories.Rosen.Incoherent.Core Cl using (τ[iMR2])
open import Categories.Rosen.Incoherent.Iterated Cl using (iMRSᴵᴵ;comp;deg₀²;deg₂²)
open import Categories.Rosen.Incoherent.Functors Cl 

open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism; niHelper; _ⓘˡ_; _ⓘʳ_;_ⓘᵥ_)

-- The three simplex categories.  C is lifted only to place all three
-- categories at the common universe levels required by Cats.
𝟘-simplex : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
𝟘-simplex = liftC ℓ (o ⊔ e) 0ℓ C

𝟙-simplex : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
𝟙-simplex = τ[iMR2]

𝟚-simplex : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
𝟚-simplex = iMRSᴵᴵ


l : Functor C 𝟘-simplex
l = liftF ℓ (o ⊔ e) 0ℓ C

-- The intended fields are 𝟘-simplex, 𝟙-simplex, and 𝟚-simplex.
-- The face, degeneracy, and simplicial-identity fields are left for the
-- pointwise development.
iMRSᴵᴵ-defines-truncated-simplicial-object :
  TruncatedSimplicialObject (Cats (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e)
iMRSᴵᴵ-defines-truncated-simplicial-object = record
  { X₀ = liftC ℓ (o ⊔ e) 0ℓ C
  ; X₁ = τ[iMR2]
  ; X₂ = iMRSᴵᴵ
  ; d₀¹ = l ∘F [_]A
  ; d₁¹ = l ∘F [_]B
  ; d₀² = deg₀²
  ; d₁² = comp
  ; d₂² = deg₂²
  ; s₀⁰ = {!   !}
  ; s₀¹ = {!   !}
  ; s₁¹ = {!   !}
  ; d₀¹-s₀⁰ = {!   !}
  ; d₁¹-s₀⁰ = {!   !}
  ; face-face₀₁ = niHelper (record 
    { η = λ X → Level.lift (C .Category.id) 
    ; η⁻¹ = λ X → Level.lift (C .Category.id) 
    ; commute = λ f → Level.lift {!   !} 
    ; iso = λ X → record
      { isoˡ = Level.lift (C .Category.identityˡ)
      ; isoʳ = Level.lift (C .Category.identity²)
      } 
    })
  ; face-face₀₂ = niHelper (record 
    { η = λ X → Level.lift (C .Category.id) 
    ; η⁻¹ = λ X → Level.lift (C .Category.id) 
    ; commute = λ f → Level.lift {!   !} 
    ; iso = λ X → record
      { isoˡ = Level.lift (C .Category.identityˡ)
      ; isoʳ = Level.lift (C .Category.identity²)
      } 
    })
  ; face-face₁₂ = niHelper (record 
    { η = λ X → Level.lift (C .Category.id) 
    ; η⁻¹ = λ X → Level.lift (C .Category.id)  
    ; commute = λ f → Level.lift {!   !} 
    ; iso = λ X → record
      { isoˡ = Level.lift (C .Category.identityˡ)
      ; isoʳ = Level.lift (C .Category.identity²)
      } 
    })
  ; degen-degen₀₀ = {!   !}
  ; d₀²-s₀¹ = {!   !}
  ; d₁²-s₀¹ = {!   !}
  ; d₁²-s₁¹ = {!   !}
  ; d₂²-s₁¹ = {!   !}
  ; face-degen₀₁ = {!   !}
  ; face-degen₂₀ = {!   !}
  }
