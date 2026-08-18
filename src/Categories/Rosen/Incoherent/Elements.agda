{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Incoherent.Elements {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

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

open import Categories.Rosen.Incoherent.Core Cl

-- twiMR2⇒: twisted morphisms of the incoherent category of elements.
record twiMR2⇒ (X Y : iMR2₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2₀ X
  module Y = iMR2₀ Y
  module ξX = iMR2 X.ξ
  module ξY = iMR2 Y.ξ
  field
    l : Y.A ⇒ X.A
    r : X.B ⇒ Y.B
    eqf : r ∘ ξX.f ∘ l ≈ ξY.f
    eqΦ : ξY.Φ ∘ r ≈ [ l , r ]₁ ∘ ξX.Φ

-- τ'[iMR2]: twisted category of incoherent (M,R)-systems.
τ'[iMR2] : Category (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e 
τ'[iMR2] = record
  { Obj = iMR2₀
  ; _⇒_ = λ s t → twiMR2⇒ s t
  ; _≈_ = λ f g → let open twiMR2⇒ in f .l ≈ g .l × f .r ≈ g .r
  ; id = record 
    { l = id 
    ; r = id 
    ; eqf = trans identityˡ identityʳ 
    ; eqΦ = id-swap ○ Equiv.sym [-,-].identity ⟩∘⟨refl 
    }
  ; _∘_ = λ f g → 
    let module f = twiMR2⇒ f  
        module g = twiMR2⇒ g 
        module Hom  {A} = Functor (appʳ [-,-] A)
        module Hom' {A} = Functor (appˡ [-,-] A)
    in record 
      { l = g.l ∘ f.l 
      ; r = f.r ∘ g.r 
      ; eqf = assoc ○ refl⟩∘⟨ rw-3-1 g.eqf ○ f.eqf 
      ; eqΦ = pullˡ C f.eqΦ ○ pullʳ C g.eqΦ ○ pullˡ C (Equiv.sym [-,-].homomorphism) }
  ; assoc = sym-assoc , assoc
  ; sym-assoc = assoc , sym-assoc
  ; identityˡ = identityʳ , identityˡ
  ; identityʳ = identityˡ , identityʳ
  ; identity² = identityˡ , identity²
  ; equiv = record { refl = refl , refl ; sym = λ {x} {y} z → sym (z .proj₁) , sym (z .proj₂) ; trans = λ {i} {j} {k} z z₁ → trans (z .proj₁) (z₁ .proj₁) , trans (z .proj₂) (z₁ .proj₂) }
  ; ∘-resp-≈ = λ x x₁ → ∘-resp-≈ (x₁ .proj₁) (x .proj₁) , ∘-resp-≈ (x .proj₂) (x₁ .proj₂)
  }

open import Categories.Category.Construction.TwistedArrow C renaming (Morphism to tMorphism; Morphism⇒ to tMorphism⇒)

𝕃 : Functor τ'[iMR2] TwistedArrow
𝕃 = record
  { F₀ = λ x → let module x = iMR2₀ x in (record { arr = iMR2.f x.ξ })
  ; F₁ = λ f → let module f = twiMR2⇒ f in mor⇒ f.eqf
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x
  }

ℝ : Functor τ'[iMR2] Arr.Arrow
ℝ = record
  { F₀ = λ x → let module x = iMR2₀ x in (record { dom = x.B ; cod = [ x.A , x.B ]₀ ; arr = iMR2.Φ x.ξ })
  ; F₁ = λ f → let module f = twiMR2⇒ f in mor⇒ (sym f.eqΦ)
  ; identity = refl , [-,-].identity
  ; homomorphism = refl , [-,-].homomorphism
  ; F-resp-≈ = λ z → z .proj₂ , [-,-].F-resp-≈ z
  }