{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (Level; 0ℓ; _⊔_; suc; lift; Lift)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor;_∘F_)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)

module Categories.Rosen.Incoherent.IteratedTruncatedSimplicialObject
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

open import Categories.Rosen.Incoherent.Core Cl using (τ[iMR2];⟪_,_⟫;iMR2;iMR2₀;iMR2⇒)
open import Categories.Rosen.Incoherent.Iterated Cl using (iMRSᴵᴵ;comp;deg₀²;deg₂²;iMRSᴵᴵ⇒)
open import Categories.Rosen.Incoherent.Functors Cl

open Category C

-- The three simplex categories.  C is lifted only to place all three
-- categories at the common universe levels required by Cats.
𝟘-simplex : Category (suc o) (suc o) o
𝟘-simplex = liftC o (suc o) 0ℓ C

-- 𝟙-simplex : Category (suc o) (suc o) o
-- 𝟙-simplex = τ[iMR2]

-- 𝟚-simplex : Category (suc o) (suc o) o
-- 𝟚-simplex = iMRSᴵᴵ
open import Categories.Morphism.Reasoning as MR
open HomReasoning
open MR

l : Functor C 𝟘-simplex
l = liftF o (suc o) 0ℓ C

open import Data.Product using (_,_; Σ)


open import Data.Unit.Polymorphic using (⊤; tt)

ιMR2 : ∀ {A} → iMR2 A A
ιMR2 = ⟪ (λ z → z) , (λ z z₁ → z) ⟫

⊤MR2 : ∀ {A} → iMR2 A ⊤
⊤MR2 = ⟪ (λ z → tt) , (λ z z₁ → tt) ⟫

uniq : {A : Set o} → (A → (⊤ {o}))
uniq {A} a = tt

bang : {A : Set o} → (f g : A → (⊤ {o})) → f ≡ g
bang f g = ≡-refl

s₀⁰ : Functor 𝟘-simplex τ[iMR2]
s₀⁰ = record
  { F₀ = λ { (lift A) → record { A = A ; B = A ; ξ = ιMR2 } }
  ; F₁ = λ { (lift f) → record { l = f ; r = f ; eqf = ≡-refl ; eqΦ = ≡-refl } }
  ; identity = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z →
      z .Lift.lower , (λ {x} → z .Lift.lower)
  }

s₀¹ : Functor τ[iMR2] iMRSᴵᴵ
s₀¹ = record
  { F₀ = λ x → let module x = iMR2₀ x in record
    { A = x.A
    ; B = x.B
    ; Y = x.B
    ; ξ₁ = x.ξ
    ; ξ₂ = ιMR2
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
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z , z .Data.Product.proj₂ , (λ {x} → z .Data.Product.proj₂)
  }

s₁¹ : Functor τ[iMR2] iMRSᴵᴵ
s₁¹ = record
  { F₀ = λ x → let module x = iMR2₀ x in record
    { A = x.A
    ; B = x.A
    ; Y = x.B
    ; ξ₁ = ιMR2
    ; ξ₂ = x.ξ
    }
  ; F₁ = λ f → let module f = iMR2⇒ f in record
    { k = record
      { l = f.l
      ; r = f.r
      ; eqf = f.eqf
      ; eqΦ = f.eqΦ
      }
    ; h = record
      { l = f.l
      ; r = f.l
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

-- The category-valued simplicial object has the following three levels.
--
-- The remaining holes cannot be filled for the present incoherent
-- definitions, regardless of which canonical MR2 object is used for a
-- degeneracy:
--
-- * If s₀⁰ uses ⊤MR2 : iMR2 A ⊤, then its two endpoint functors are A and
--   ⊤.  Hence d₀¹ ∘ s₀⁰ is the identity, but d₁¹ ∘ s₀⁰ asks for a natural
--   isomorphism ⊤ ≅ A for every set A.
--
-- * If s₀⁰ uses ιMR2 : iMR2 A A instead, both endpoint identities can hold.
--   However, for ξ = (f , Φ), the usual choice
--   s₀¹ ξ = (ξ , ιMR2) has composite
--
--       comp (s₀¹ ξ) = (id ∘ f , [ f , id ]₁ ∘ ιMR2.Φ).
--
--   In Sets, the second component is the constant map (b , a) ↦ b.  The
--   identity d₁² ∘ s₀¹ ≈ id would therefore require every incoherent
--   Φ : B → (A → B) to be this constant map.  That is false in general.
--
-- Thus ιMR2 is the correct endpoint degeneracy, but the simplicial object
-- requires either coherent MR2 systems, a restriction to normalized Φ, or
-- a weaker notion of morphism that forgets the Φ-compatibility.  The two
-- sorry terms in d₁²-s₀¹ below mark the forward and inverse forms of exactly
-- this unprovable equality.
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
  ; d₀¹-s₀⁰ = NI.refl
  ; d₁¹-s₀⁰ = NI.refl
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
          ; eqΦ = λ {x} → sorry
          }
      ; η⁻¹ = λ _ → record
          { l = id
          ; r = id
          ; eqf = λ {x} → ≡-refl
          ; eqΦ = λ {x} → sorry
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
