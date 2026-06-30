{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_;lift;lower;zero;suc)

open import Data.Product using (Σ;_,_; proj₁; proj₂; _×_)
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

module Categories.Rosen.Incoherent.Core {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

-- open 𝒞
import Reason
open Reason C

import Categories.Morphism.Reasoning as MR

open HomReasoning
open MR

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [_,_]₁; Hom[-⊗_,-]; Hom[-,[_,-]]; Hom-NI)

module Arr = Categories.Category.Construction.Arrow C

record iMR2 (A B : Obj) : Set (o ⊔ ℓ) where
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    ϕ : B ⇒ [ A , B ]₀

record iMR2₀ : Set (o ⊔ ℓ) where
  field
    A B : Obj
    ξ : iMR2 A B

record iMR2⇒ (X Y : iMR2₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2₀ X
  module Y = iMR2₀ Y
  module ξX = iMR2 X.ξ
  module ξY = iMR2 Y.ξ
  field
    l : X.A ⇒ Y.A
    r : X.B ⇒ Y.B
    eqf : r ∘ ξX.f ≈ ξY.f ∘ l
    eqϕ : [ l , id ]₁ ∘ ξY.ϕ ∘ r ≈ [ id , r ]₁ ∘ ξX.ϕ

-- total category of incoherent MR systems
τ[iMR2] : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e 
τ[iMR2] = record
  { Obj = iMR2₀
  ; _⇒_ = λ s t → iMR2⇒ s t
  ; _≈_ = λ f g → let open iMR2⇒ in f .l ≈ g .l × f .r ≈ g .r
    -- let module f = iMR2⇒ f  
    --     module g = iMR2⇒ g in f.l ≈ g.l × f.r ≈ g.r
  ; id = record 
    { l = id 
    ; r = id 
    ; eqf = sym-id-swap 
    ; eqϕ = id-2 
    }
  ; _∘_ = λ f g → 
    let module f = iMR2⇒ f  
        module g = iMR2⇒ g 
        module Hom  {A} = Functor (appʳ [-,-] A)
        module Hom' {A} = Functor (appˡ [-,-] A)
    in record { l = f.l ∘ g.l 
              ; r = f.r ∘ g.r 
              ; eqf = assoc ○ refl⟩∘⟨ g.eqf ○ rw-2-1 f.eqf ○ assoc 
              ; eqϕ = begin [ f.l ∘ g.l , id ]₁ ∘ f.ξY.ϕ ∘ f.r ∘ g.r             ≈⟨ Hom.homomorphism ⟩∘⟨refl ⟩ 
                            ([ g.l , id ]₁ ∘ [ f.l , id ]₁) ∘ f.ξY.ϕ ∘ f.r ∘ g.r ≈⟨ assoc ⟩ 
                            [ g.l , id ]₁ ∘ [ f.l , id ]₁ ∘ f.ξY.ϕ ∘ f.r ∘ g.r   ≈⟨ refl⟩∘⟨ rw-3-1 f.eqϕ ⟩ 
                            [ g.l , id ]₁ ∘ ([ id , f.r ]₁ ∘ g.ξY.ϕ) ∘ g.r       ≈⟨ refl⟩∘⟨ assoc ⟩ 
                            [ g.l , id ]₁ ∘ [ id , f.r ]₁ ∘ g.ξY.ϕ ∘ g.r         ≈⟨ sym-assoc ○ Equiv.sym [ [-,-] ]-commute ⟩∘⟨refl ⟩ 
                            ([ id , f.r ]₁ ∘ [ g.l , id ]₁) ∘ g.ξY.ϕ ∘ g.r       ≈⟨ assoc ○ refl⟩∘⟨ g.eqϕ ⟩ 
                            [ id , f.r ]₁ ∘ [ id , g.r ]₁ ∘ g.ξX.ϕ               ≈⟨ pullˡ C (Equiv.sym Hom'.homomorphism) ⟩ 
                            [ id , f.r ∘ g.r ]₁ ∘ g.ξX.ϕ ∎ 
    }
  ; assoc = λ { {A} {B} {C} {D} {f} {g} {h} → 
    ( assoc {f = iMR2⇒.l f} {g = iMR2⇒.l g} {h = iMR2⇒.l h}) 
    , (assoc {f = iMR2⇒.r f} {g = iMR2⇒.r g} {h = iMR2⇒.r h}) } -- assoc , assoc
  ; sym-assoc = λ { {A} {B} {C} {D} {f} {g} {h} → 
    ( sym-assoc {f = iMR2⇒.l f} {g = iMR2⇒.l g} {h = iMR2⇒.l h}) 
    , (sym-assoc {f = iMR2⇒.r f} {g = iMR2⇒.r g} {h = iMR2⇒.r h}) } -- sym-assoc , sym-assoc 
  ; identityˡ = λ { {A} {B} {f} → identityˡ {f = iMR2⇒.l f} 
                  , identityˡ {f = iMR2⇒.r f} 
                  } -- identityˡ , identityˡ 
  ; identityʳ = λ { {A} {B} {f} → identityʳ {f = iMR2⇒.l f} 
                  , identityʳ {f = iMR2⇒.r f} 
                  } -- identityʳ , identityʳ 
  ; identity² = identity² , identity² 
  ; equiv = record 
    { refl = refl , refl 
    ; sym = λ x → (sym (proj₁ x)) , (sym (proj₂ x)) 
    ; trans = λ { (eq-l , eq-r) (eq'-l , eq'-r) → (trans eq-l eq'-l) , (trans eq-r eq'-r) }
    }
  ; ∘-resp-≈ = λ { (eq-l , eq-r) (eq'-l , eq'-r) → (∘-resp-≈ eq-l eq'-l) , (∘-resp-≈ eq-r eq'-r) }
  }