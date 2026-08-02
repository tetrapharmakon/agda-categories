{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (Level; 0ℓ; _⊔_; suc)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor;_∘F_)
open import Categories.Category.Instance.Sets using (Sets)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)

module Categories.Rosen.Incoherent.IteratedTruncatedSimplicialObject
  (o : Level) where

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

open import Categories.Rosen.Incoherent.Core Cl using (τ[iMR2];⟪_,_⟫;iMR2;iMR2₀;iMR2⇒)
open import Categories.Rosen.Incoherent.Iterated Cl using (iMRSᴵᴵ;comp;deg₀²;deg₂²)
open import Categories.Rosen.Incoherent.Functors Cl
-- open import Categories.Rosen.Incoherent.CartesianAdjoints o

-- The three simplex categories.  C is lifted only to place all three
-- categories at the common universe levels required by Cats.
𝟘-simplex : Category (suc o) (suc o) o
𝟘-simplex = liftC o (suc o) 0ℓ C

-- 𝟙-simplex : Category (suc o) (suc o) o
-- 𝟙-simplex = τ[iMR2]

-- 𝟚-simplex : Category (suc o) (suc o) o
-- 𝟚-simplex = iMRSᴵᴵ


l : Functor C 𝟘-simplex
l = liftF o (suc o) 0ℓ C

open import Data.Product using (_,_; Σ)

s₀⁰ : Functor 𝟘-simplex τ[iMR2]
s₀⁰ = record
  { F₀ = λ x → record { A = x .Level.lower ; B = x .Level.lower ; ξ = ⟪ (λ z → z) , (λ z z₁ → z) ⟫ }
  ; F₁ = λ f → record { l = f .Level.lower ; r = f .Level.lower ; eqf = ≡-refl ; eqΦ = ≡-refl }
  ; identity = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ x → x .Level.lower , x .Level.lower
  }

trivialMR2 : ∀ {A} → iMR2 A A
trivialMR2 = ⟪ (λ z → z) , (λ z z₁ → z) ⟫

s₀¹ : Functor τ[iMR2] iMRSᴵᴵ
s₀¹ = record
  { F₀ = λ x → let module x = iMR2₀ x in record
    { A = x.A
    ; B = x.B
    ; Y = x.B
    ; ξ₁ = x.ξ
    ; ξ₂ = trivialMR2
    }
  ; F₁ = λ f → let module f = iMR2⇒ f in record
    { h = record
      { l = f.l
      ; r = f.r
      ; eqf = f.eqf
      ; eqΦ = f.eqΦ
      }
    ; k = record
      { l = f.r
      ; r = f.r
      ; eqf = λ {x} → ≡-refl
      ; eqΦ = λ {x} → ≡-refl
      }
    ; hᵣ≈kₗ = λ {x} → ≡-refl }
  ; identity = λ {A} →
      ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
      (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
      ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
      (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z →
      z , z .Data.Product.proj₂ , z .Data.Product.proj₂
  }

s₁¹ : Functor τ[iMR2] iMRSᴵᴵ
s₁¹ = record
  { F₀ = λ x → let module x = iMR2₀ x in record
    { A = x.A
    ; B = x.A
    ; Y = x.B
    ; ξ₁ = trivialMR2
    ; ξ₂ = x.ξ
    }
  ; F₁ = λ f → let module f = iMR2⇒ f in record
    { k = record
      { l = f.l -- f.l
      ; r = f.r -- f.l
      ; eqf = f.eqf -- f.eqf
      ; eqΦ = f.eqΦ -- f.eqΦ
      }
    ; h = record
      { l = f.l -- f.l
      ; r = f.l -- f.r
      ; eqf = λ {x} → ≡-refl
      ; eqΦ = λ {x} → ≡-refl
      }
    ; hᵣ≈kₗ = λ {x} → ≡-refl }
  ; identity = λ {A} →
      ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
      (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
      ((λ {x} → ≡-refl) , (λ {x} → ≡-refl)) ,
      (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z →
      (z .Data.Product.proj₁ , z .Data.Product.proj₁) , z
  }

-- The intended fields are 𝟘-simplex, 𝟙-simplex, and 𝟚-simplex.
-- The face, degeneracy, and simplicial-identity fields are left for the
-- pointwise development.
iMRSᴵᴵ-defines-truncated-simplicial-object :
  TruncatedSimplicialObject (Cats (suc o) (suc o) o)
iMRSᴵᴵ-defines-truncated-simplicial-object = record
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
  ; d₀¹-s₀⁰ = {!   !}
  ; d₁¹-s₀⁰ = {!   !}
  ; face-face₀₁ = {!   !}
  ; face-face₀₂ = {!   !}
  ; face-face₁₂ = {!   !}
  ; degen-degen₀₀ = {!   !}
  ; d₀²-s₀¹ = {!   !}
  ; d₁²-s₀¹ = {!   !}
  ; d₁²-s₁¹ = {!   !}
  ; d₂²-s₁¹ = {!   !}
  ; face-degen₀₁ = {!   !}
  ; face-degen₂₀ = {!   !}
  }
