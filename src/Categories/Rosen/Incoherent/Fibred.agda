{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.Fibred {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Fibred incoherent (M,R)-systems: the fibre over a fixed domain A.
-- Reindexing along u : A ⇒ A' is functorial (contravariant) in A.

open import Data.Product using (_,_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.Rosen.Incoherent.Core Cl

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₁)
open HomReasoning
open MR



-- iMR2ᴿ₀: object of the fibre over A: a codomain B plus an iMR2 A B.
record iMR2ᴿ₀ (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B : Obj
    ξ : iMR2 A B 

-- iMR2ᴿ⇒: morphisms in the fibre over A: v : X.B ⇒ Y.B compatible with f and ϕ.
record iMR2ᴿ⇒ {A : Obj} (X Y : iMR2ᴿ₀ A) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2ᴿ₀ X
  module Y = iMR2ᴿ₀ Y   
  module ξX = iMR2 X.ξ  
  module ξY = iMR2 Y.ξ
  field
    v : X.B ⇒ Y.B
    eqf : v ∘ ξX.f ≈ ξY.f
    eqϕ : [ id , v ]₁ ∘ ξX.ϕ ≈ ξY.ϕ ∘ v

-- iMR2ᴿ A: the fibre category over A of the incoherent MRS profunctor.
iMR2ᴿ : (A : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
iMR2ᴿ A = record
  { Obj = iMR2ᴿ₀ A
  ; _⇒_ = λ X Y → iMR2ᴿ⇒ {A} X Y
  ; _≈_ = λ p q → let module p = iMR2ᴿ⇒ p 
                      module q = iMR2ᴿ⇒ q
                  in p.v ≈ q.v
  ; id = record 
    { v = id 
    ; eqf = id-0 
    ; eqϕ = Equiv.trans (cancel (Functor.identity [-,-])) (sym-id-1) }
  ; _∘_ = λ p q → 
    let module p = iMR2ᴿ⇒ p 
        module q = iMR2ᴿ⇒ q
    in record 
      { v = p.v ∘ q.v
      ; eqf = pullʳ C q.eqf ∙ p.eqf 
      ; eqϕ = let module Hom = Functor [-,-]
                  module Hom[1-] {A} = Functor (appˡ [-,-] A)
                  module Hom[-1] {A} = Functor (appʳ [-,-] A) 
              in (begin [ id , p.v ∘ q.v ]₁ ∘ q.ξX.ϕ ≈⟨ pushˡ C Hom[1-].homomorphism ⟩  
                        [ id , p.v ]₁ ∘ [ id , q.v ]₁ ∘ q.ξX.ϕ ≈⟨ refl⟩∘⟨ q.eqϕ ⟩  
                        [ id , p.v ]₁ ∘ q.ξY.ϕ ∘ q.v ≈⟨ rw-2-1 p.eqϕ ∙ assoc ⟩  
                        p.ξY.ϕ ∘ p.v ∘ q.v ∎) 
      }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ eq eq' → ∘-resp-≈ eq eq'
  }

private
 variable
  A A' B B' : Obj

-- MRSreindex u: reindexing functor iMR2ᴿ A' → iMR2ᴿ A along u : A ⇒ A'.
MRSreindex : (u : A ⇒ A') → Functor (iMR2ᴿ A') (iMR2ᴿ A)
MRSreindex {A} {A'} u = record
  { F₀ = λ { x → 
    let module x = iMR2ᴿ₀ x 
    in record 
    { B = x.B
    ; ξ = ⟪ iMR2.f x.ξ ∘ u , [ u , id ]₁ ∘ iMR2.ϕ x.ξ ⟫ 
    }}
  ; F₁ = λ { {x} {y} f → 
      let module x   = iMR2ᴿ₀ x
          module ξx  = iMR2 x.ξ
          module y   = iMR2ᴿ₀ y
          module ξy  = iMR2 y.ξ
          module f = iMR2ᴿ⇒ f 
      in record 
    { v = f.v
    ; eqf = begin f.v ∘ f.ξX.f ∘ u   ≈⟨ sym-assoc ⟩ 
                  (f.v ∘ f.ξX.f) ∘ u ≈⟨ f.eqf ⟩∘⟨refl ⟩ 
                  f.ξY.f ∘ u         ∎
    ; eqϕ = begin [ id , f.v ]₁ ∘ [ u , id ]₁ ∘ f.ξX.ϕ ≈⟨ sym-assoc ∙ ([ [-,-] ]-commute ⟩∘⟨refl) ∙ assoc ⟩
                  [ u , id ]₁ ∘ [ id , f.v ]₁ ∘ f.ξX.ϕ ≈⟨ (refl⟩∘⟨ f.eqϕ) ∙ sym-assoc ⟩ 
                  ([ u , id ]₁ ∘ f.ξY.ϕ) ∘ f.v ∎
    }}
  ; identity = λ {A} → refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → refl
  ; F-resp-≈ = λ x → x
  }