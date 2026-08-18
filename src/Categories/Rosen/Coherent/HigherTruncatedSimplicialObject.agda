{-# OPTIONS --without-K --allow-unsolved-metas --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor;_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
open import Level using (Level; 0ℓ; _⊔_; suc; lift; Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)

module Categories.Rosen.Coherent.HigherTruncatedSimplicialObject
  (o : Level) where

private
  postulate
    sorry : ∀ {u} {A : Set u} → A

open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Lift using (liftC;liftF)
open import Categories.TruncatedSimplicialObject using (TruncatedSimplicialObject)

open import Categories.Rosen.Cartesian.Sets
open Sets-MonoidalClosed {o}

private
  C : Category (suc o) o o
  C = Sets o

  M = Sets-Monoidal
  Cl = Sets-Closed

open import Categories.Rosen.Coherent.Core Cl
open import Categories.Rosen.Coherent.HigherMRS Cl
open import Categories.Rosen.Coherent.Tabulator Cl

open Category C

-- The three simplex categories.  C is lifted only to place all three
-- categories at the common universe levels required by Cats.
𝟘-simplex : Category (suc o) (suc o) o
𝟘-simplex = liftC o (suc o) 0ℓ C

open import Categories.Morphism.Reasoning as MR
open HomReasoning
open MR

l : Functor C 𝟘-simplex
l = liftF o (suc o) 0ℓ C


MRS-defines-truncated-simplicial-object :
  TruncatedSimplicialObject (Cats (suc o) (suc o) o)
MRS-defines-truncated-simplicial-object = record
  { X₀ = 𝟘-simplex
  ; X₁ = 𝕋MRS
  ; X₂ = MRS3
  ; d₀¹ = {!  !}
  ; d₁¹ = {!  !}
  ; d₀² = {!  !}
  ; d₁² = {!  !}
  ; d₂² = {!  !}
  ; s₀⁰ = {!  !}
  ; s₀¹ = {!  !}
  ; s₁¹ = {!  !}
  ; d₀¹-s₀⁰ = {!  !}
  ; d₁¹-s₀⁰ = {!  !}
  ; face-face₀₁ = {!  !}
  ; face-face₀₂ = {!  !}
  ; face-face₁₂ = {!  !}
  ; degen-degen₀₀ = {!  !}
  ; d₀²-s₀¹ = {!  !}
  ; d₁²-s₀¹ = {!  !}
  ; d₁²-s₁¹ = {!  !}
  ; d₂²-s₁¹ = {!  !}
  ; face-degen₀₁ = {!  !}
  ; face-degen₂₀ = {!  !}
  } 

{-
  { X₀ = 𝟘-simplex
  ; X₁ = τ[iMR2]
  ; X₂ = iMRSᴵᴵ
  ; d₀¹ = l ∘F [_]A
  ; d₁¹ = l ∘F [_]B
  ; d₀² = deg₀²
  ; d₁² = comp
  ; d₂² = deg₂²
  ; s₀⁰ = s₀⁰
  ; s₀¹ = s₀¹
  ; s₁¹ = s₁¹
  ; d₀¹-s₀⁰ = NI.refl
  ; d₁¹-s₀⁰ = {!   !}
  -- Goal: construct a natural isomorphism
  -- (l ∘F [_]B ∘F s₀⁰) ≃ idF.  Objectwise this requires ⊤ ≅ A.
  -- Goal: prove that the second endpoint of the degenerate 1-simplex
  -- is naturally isomorphic to the original set. With the current
  -- definition of s₀⁰, this asks for ⊤ ≅ A for every set A.
  ; face-face₀₁ = NI.refl
  ; face-face₀₂ = NI.niHelper record
      { η = λ _ → lift (Category.id C)
       ; η⁻¹ = λ _ → lift (Category.id C)
       ; commute = λ {X} {Y} f →
           let module f = iMRSᴵᴵ⇒ f in
           lift {o} (λ {x} → ≡-sym (f.hᵣ≈kₗ {x}))
      ; iso = λ _ → record
          { isoˡ = lift identity²
          ; isoʳ = lift identity²
          }
      }
  ; face-face₁₂ = NI.refl
  ; degen-degen₀₀ = niHelper (record
    { η = λ X →
        record
        { h =
            record
            { l = λ z → z
            ; r = λ z → z
            ; eqf = λ {x} → ≡-refl
            ; eqΦ = λ {x} → ≡-refl
            }
        ; k =
            record
            { l = λ z → z
            ; r = λ z → z
            ; eqf = λ {x} → ≡-refl
            ; eqΦ = λ {x} → ≡-refl
            }
        ; hᵣ≈kₗ = λ {x} → ≡-refl
        }
    ; η⁻¹ = λ X →
        record
        { h =
            record
            { l = λ z → z
            ; r = λ z → z
            ; eqf = λ {x} → ≡-refl
            ; eqΦ = λ {x} → ≡-refl
            }
        ; k =
            record
            { l = λ z → z
            ; r = λ z → z
            ; eqf = λ {x} → ≡-refl
            ; eqΦ = λ {x} → ≡-refl
            }
        ; hᵣ≈kₗ = λ {x} → ≡-refl
        }
    ; commute = λ {X} {Y} f →
        ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
        (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
    ; iso = λ X →
        record
        { isoˡ =
            ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
            (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
        ; isoʳ =
            ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
            (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
        }
    })
  -- Goal: construct a natural isomorphism
  -- (s₀¹ ∘F s₀⁰) ≃ (s₁¹ ∘F s₀⁰).
  ; d₀²-s₀¹ = NI.refl
  ; d₁²-s₀¹ = NI.niHelper record
      { η = λ _ → record
          { l = id
          ; r = id
          ; eqf = λ {x} → ≡-refl
          ; eqΦ = λ {x} → {!   !} -- identityʳ ○ refl⟩∘⟨ λ {x = x₂} → ≡-refl
          -- Goal: prove [id,id]₁ ∘ Φ ∘ id ≈ [id,id]₁ ∘ Φ₀.
          }
      ; η⁻¹ = λ _ → record
          { l = id
          ; r = id
          ; eqf = λ {x} → ≡-refl
          ; eqΦ = λ {x} → {!   !} -- identityʳ ○ refl⟩∘⟨ λ {x = x₂} → ≡-refl
          -- Goal: prove the inverse Φ-square,
          -- [id,id]₁ ∘ Φ₀ ∘ id ≈ [id,id]₁ ∘ Φ.
          }
      ; commute = λ _ → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
      ; iso = λ _ → record
          { isoˡ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
          ; isoʳ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
          }
      }
  ; d₁²-s₁¹ = NI.niHelper record
      { η = λ _ → record
          { l = id
          ; r = id
          ; eqf = λ {x} → ≡-refl
          ; eqΦ = λ {x} → ≡-refl
          }
      ; η⁻¹ = λ _ → record
          { l = id
          ; r = id
          ; eqf = λ {x} → ≡-refl
          ; eqΦ = λ {x} → ≡-refl
          }
      ; commute = λ _ → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
      ; iso = λ _ → record
          { isoˡ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
          ; isoʳ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
          }
      }
  ; d₂²-s₁¹ = NI.refl
  ; face-degen₀₁ = niHelper (record
    { η = λ X →
        record
        { l = λ z → z
        ; r = λ z → z
        ; eqf = λ {x} → ≡-refl
        ; eqΦ = λ {x} → ≡-refl
        }
    ; η⁻¹ = λ X →
        record
        { l = λ z → z
        ; r = λ z → z
        ; eqf = λ {x} → ≡-refl
        ; eqΦ = λ {x} → ≡-refl
        }
    ; commute = λ {X} {Y} f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
    ; iso = λ X →
        record
        { isoˡ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
        ; isoʳ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
        }
    })
  -- Goal: prove the natural-isomorphism equation
  -- d₀² ∘F s₁¹ ≃ s₀⁰ ∘F d₀¹.
  ; face-degen₂₀ = niHelper (record
    { η = λ X →
        record
        { l = λ z → z
        ; r = λ z → z
        ; eqf = λ {x} → ≡-refl
        ; eqΦ = λ {x} → ≡-refl
        }
    ; η⁻¹ = λ X →
        record
        { l = λ z → z
        ; r = λ z → z
        ; eqf = λ {x} → ≡-refl
        ; eqΦ = λ {x} → ≡-refl
        }
    ; commute = λ {X} {Y} f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
    ; iso = λ X →
        record
        { isoˡ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
        ; isoʳ = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
        }
    })
  -- Goal: prove the natural-isomorphism equation
  -- d₂² ∘F s₀¹ ≃ s₀⁰ ∘F d₁¹.
  }
-}