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

record iMR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    ϕ : B ⇒ [ A , B ]₀

-- iMR2 (_ , B) è funtoriale per ogni B fissato; C^op --> Setoids
-- iMR2 (A , _) forse induce un *profuntore* tra iMR2(A,B) e iMR2(A, B')...

record iMR2ᴸ₀ (B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A : Obj
    ξ : iMR2 A B 

record iMR2ᴸ⇒ {B : Obj} (X Y : iMR2ᴸ₀ B) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2ᴸ₀ X
  module Y = iMR2ᴸ₀ Y   
  module ξX = iMR2 X.ξ  
  module ξY = iMR2 Y.ξ
  field
    u : X.A ⇒ Y.A
    eqf : ξX.f ≈ ξY.f ∘ u
    eqϕ : ξX.ϕ ≈ [ u , id ]₁ ∘ ξY.ϕ

-- funtoriale
iMR2ᴸ : (B : Obj) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
iMR2ᴸ B = record
  { Obj = iMR2ᴸ₀ B
  ; _⇒_ = λ X Y → iMR2ᴸ⇒ {B} X Y
  ; _≈_ = λ p q → let module p = iMR2ᴸ⇒ p 
                      module q = iMR2ᴸ⇒ q
                  in p.u ≈ q.u
  ; id = record 
    { u = id 
    ; eqf = sym-id-1 
    ; eqϕ = Equiv.sym (cancel (Functor.identity [-,-])) 
    }
  ; _∘_ = λ p q → 
    let module p = iMR2ᴸ⇒ p 
        module q = iMR2ᴸ⇒ q
    in record 
      { u = p.u ∘ q.u 
      ; eqf = q.eqf ∙ rw-1-2 p.eqf 
      ; eqϕ = let module Hom = Functor [-,-]
                  module Hom[1-] {A} = Functor (appˡ [-,-] A)
                  module Hom[-1] {A} = Functor (appʳ [-,-] A) 
              in Equiv.sym (begin [ p.u ∘ q.u , id ]₁ ∘ p.ξY.ϕ ≈⟨ pushˡ C Hom[-1].homomorphism ⟩ 
                                  [ q.u , id ]₁ ∘ [ p.u , id ]₁ ∘ p.ξY.ϕ ≈⟨ Equiv.sym (refl⟩∘⟨ p.eqϕ) ⟩ 
                                  [ q.u , id ]₁ ∘ q.ξY.ϕ ≈⟨ Equiv.sym q.eqϕ ⟩ 
                                  q.ξX.ϕ ∎)
      }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ eq eq' → ∘-resp-≈ eq eq'
  }


record iMR2ᴿ₀ (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B : Obj
    ξ : iMR2 A B 

record iMR2ᴿ⇒ {A : Obj} (X Y : iMR2ᴿ₀ A) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2ᴿ₀ X
  module Y = iMR2ᴿ₀ Y   
  module ξX = iMR2 X.ξ  
  module ξY = iMR2 Y.ξ
  field
    v : X.B ⇒ Y.B
    eqf : v ∘ ξX.f ≈ ξY.f
    eqϕ : [ id , v ]₁ ∘ ξX.ϕ ≈ ξY.ϕ ∘ v

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

left : (u : A ⇒ A') → Functor (iMR2ᴿ A') (iMR2ᴿ A)
left u = record
  { F₀ = λ { x → 
    let module x = iMR2ᴿ₀ x 
    in record 
    { B = x.B
    ; ξ = ⟪ iMR2.f x.ξ ∘ u , [ u , id ]₁ ∘ iMR2.ϕ x.ξ ⟫ 
    }}
  ; F₁ = λ f → let module f = iMR2ᴿ⇒ f in record 
    { v = {!  !} -- f.v? 
    ; eqf = {!  !} 
    ; eqϕ = {!  !} }
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }


wrong : (v : B ⇒ B') → Functor (iMR2ᴸ B) (iMR2ᴸ B')
wrong v = record
  { F₀ = λ x → 
  let module x = iMR2ᴸ₀ x 
      module ξx = iMR2 x.ξ
  in record 
   { A = x.A 
   ; ξ = ⟪ v ∘ ξx.f , {!  !} ⟫ 
   }
  ; F₁ = {!  !}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }

right : (v : B ⇒ B') → Bifunctor (iMR2ᴸ B) (iMR2ᴸ B') (Setoids {!  !} {!  !})
right v = record
  { F₀ = λ {(x , y) → 
    let module x = iMR2ᴸ₀ x 
        module ξx = iMR2 x.ξ
        module y = iMR2ᴸ₀ y 
        module ξy = iMR2 y.ξ
    in {!  !}}
  ; F₁ = {!  !}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }