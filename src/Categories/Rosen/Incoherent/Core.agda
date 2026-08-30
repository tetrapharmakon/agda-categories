{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Incoherent.Core {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —Φ→ [A,B]
-- without the natural transformation condition of full MR2.

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₀; [_,_]₁)
open HomReasoning
open MR

module Arr = Categories.Category.Construction.Arrow C

-- iMR2: an incoherent (M,R)-system: a pair (f, Φ).
record iMR2 (A B : Obj) : Set (o ⊔ ℓ) where
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    Φ : B ⇒ [ A , B ]₀

-- iMR2₀: an object of the total category (a pair of objects plus an iMR2).
record iMR2₀ : Set (o ⊔ ℓ) where
  field
    A B : Obj
    ξ : iMR2 A B

-- iMR2⇒: morphisms of the incoherent total category.
record iMR2⇒ (X Y : iMR2₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2₀ X
  module Y = iMR2₀ Y
  module ξX = iMR2 X.ξ
  module ξY = iMR2 Y.ξ
  field
    l : X.A ⇒ Y.A
    r : X.B ⇒ Y.B
    eqf : r ∘ ξX.f ≈ ξY.f ∘ l
    eqΦ : [ l , id ]₁ ∘ ξY.Φ ∘ r ≈ [ id , r ]₁ ∘ ξX.Φ

-- τ[iMR2]: total category of incoherent (M,R)-systems.
τ[iMR2] : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e
τ[iMR2] = record
  { Obj = iMR2₀
  ; _⇒_ = λ s t → iMR2⇒ s t
  ; _≈_ = λ f g → let open iMR2⇒ in f .l ≈ g .l × f .r ≈ g .r
  ; id = record
    { l = id
    ; r = id
    ; eqf = sym-id-swap
    ; eqΦ = id-2
    }
  ; _∘_ = λ f g →
    let module f = iMR2⇒ f
        module g = iMR2⇒ g
        module Hom  {A} = Functor (appʳ [-,-] A)
        module Hom′ {A} = Functor (appˡ [-,-] A)
    in record { l = f.l ∘ g.l
              ; r = f.r ∘ g.r
              ; eqf = assoc ○ refl⟩∘⟨ g.eqf ○ rw-2-1 f.eqf ○ assoc
              ; eqΦ = begin [ f.l ∘ g.l , id ]₁ ∘ f.ξY.Φ ∘ f.r ∘ g.r             ≈⟨ Hom.homomorphism ⟩∘⟨refl ⟩
                            ([ g.l , id ]₁ ∘ [ f.l , id ]₁) ∘ f.ξY.Φ ∘ f.r ∘ g.r ≈⟨ assoc ⟩
                            [ g.l , id ]₁ ∘ [ f.l , id ]₁ ∘ f.ξY.Φ ∘ f.r ∘ g.r   ≈⟨ refl⟩∘⟨ rw-3-1 f.eqΦ ⟩
                            [ g.l , id ]₁ ∘ ([ id , f.r ]₁ ∘ g.ξY.Φ) ∘ g.r       ≈⟨ refl⟩∘⟨ assoc ⟩
                            [ g.l , id ]₁ ∘ [ id , f.r ]₁ ∘ g.ξY.Φ ∘ g.r         ≈⟨ sym-assoc ○ Equiv.sym [ [-,-] ]-commute ⟩∘⟨refl ⟩
                            ([ id , f.r ]₁ ∘ [ g.l , id ]₁) ∘ g.ξY.Φ ∘ g.r       ≈⟨ assoc ○ refl⟩∘⟨ g.eqΦ ⟩
                            [ id , f.r ]₁ ∘ [ id , g.r ]₁ ∘ g.ξX.Φ               ≈⟨ pullˡ C (Equiv.sym Hom′.homomorphism) ⟩
                            [ id , f.r ∘ g.r ]₁ ∘ g.ξX.Φ ∎
    }
  ; assoc = λ { {A} {B} {C} {D} {f} {g} {h} →
    ( assoc {f = iMR2⇒.l f} {g = iMR2⇒.l g} {h = iMR2⇒.l h})
    , (assoc {f = iMR2⇒.r f} {g = iMR2⇒.r g} {h = iMR2⇒.r h}) }
  ; sym-assoc = λ { {A} {B} {C} {D} {f} {g} {h} →
    ( sym-assoc {f = iMR2⇒.l f} {g = iMR2⇒.l g} {h = iMR2⇒.l h})
    , (sym-assoc {f = iMR2⇒.r f} {g = iMR2⇒.r g} {h = iMR2⇒.r h}) }
  ; identityˡ = λ { {A} {B} {f} → identityˡ {f = iMR2⇒.l f}
                  , identityˡ {f = iMR2⇒.r f}
                  }
  ; identityʳ = λ { {A} {B} {f} → identityʳ {f = iMR2⇒.l f}
                  , identityʳ {f = iMR2⇒.r f}
                  }
  ; identity² = identity² , identity²
  ; equiv = record
    { refl = refl , refl
    ; sym = λ x → (sym (proj₁ x)) , (sym (proj₂ x))
    ; trans = λ { (eq-l , eq-r) (eq′-l , eq′-r) → (trans eq-l eq′-l) , (trans eq-r eq′-r) }
    }
  ; ∘-resp-≈ = λ { (eq-l , eq-r) (eq′-l , eq′-r) → (∘-resp-≈ eq-l eq′-l) , (∘-resp-≈ eq-r eq′-r) }
  }
