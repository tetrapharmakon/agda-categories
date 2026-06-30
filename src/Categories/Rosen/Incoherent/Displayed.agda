{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Data.Product using (Σ;_,_; proj₁; _×_)

open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)

module Categories.Rosen.Incoherent.Displayed {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

-- open 𝒞
import Reason
open Reason C

import Categories.Morphism.Reasoning as MR

open HomReasoning
open MR

open Closed Cl using ([-,-]; [_,_]₁)

module Arr = Categories.Category.Construction.Arrow C

open import Categories.Rosen.Incoherent.Core Cl

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

private
 variable
  A A' B B' : Obj

right : (v : B ⇒ B') → Bifunctor (Category.op (iMR2ᴸ B)) (iMR2ᴸ B') (Setoids (ℓ ⊔ e) e)
right v = record
  { F₀ = λ {(x , y) → 
     let module x  = iMR2ᴸ₀ x 
         module ξx = iMR2 x.ξ
         module y  = iMR2ᴸ₀ y 
         module ξy = iMR2 y.ξ
     in record
       { Carrier = Σ (x.A ⇒ y.A) (λ u →
           (v ∘ ξx.f ≈ ξy.f ∘ u)
         × ([ id , v ]₁ ∘ ξx.ϕ ≈ [ u , id ]₁ ∘ ξy.ϕ ∘ v))
       ; _≈_ = λ p q → proj₁ p ≈ proj₁ q
       ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
       }}
  ; F₁ = λ { {(x , y)} {(x' , y')} (s , t) →
      let module x   = iMR2ᴸ₀ x
          module ξx  = iMR2 x.ξ
          module x'  = iMR2ᴸ₀ x'
          module ξx' = iMR2 x'.ξ
          module y   = iMR2ᴸ₀ y
          module ξy  = iMR2 y.ξ
          module y'  = iMR2ᴸ₀ y'
          module ξy' = iMR2 y'.ξ
          module s   = iMR2ᴸ⇒ s
          module t   = iMR2ᴸ⇒ t
          module Hom[-1] {A} = Functor (appʳ [-,-] A)
      in record
      { _⟨$⟩_ = λ { (u , (eqf , eqϕ)) →
          let u' : x'.A ⇒ y'.A
              u' = t.u ∘ u ∘ s.u
              eqf' : v ∘ ξx'.f ≈ ξy'.f ∘ u'
              eqf' = begin
                v ∘ ξx'.f                   ≈⟨ (refl⟩∘⟨ s.eqf) ∙ sym-assoc ⟩
                (v ∘ ξx.f) ∘ s.u            ≈⟨ rw eqf ∙ assoc ⟩
                ξy.f ∘ (u ∘ s.u)            ≈⟨ rw t.eqf ∙ assoc ⟩
                ξy'.f ∘ (t.u ∘ (u ∘ s.u))   ∎
              eqϕ' : [ id , v ]₁ ∘ ξx'.ϕ ≈ [ u' , id ]₁ ∘ ξy'.ϕ ∘ v
              eqϕ' = begin
                [ id , v ]₁ ∘ ξx'.ϕ                               ≈⟨ (refl⟩∘⟨ s.eqϕ) ∙ sym-assoc ⟩
                ([ id , v ]₁ ∘ [ s.u , id ]₁) ∘ ξx.ϕ              ≈⟨ (rw [ [-,-] ]-commute) ∙ assoc ⟩
                [ s.u , id ]₁ ∘ ([ id , v ]₁ ∘ ξx.ϕ)              ≈⟨ (refl⟩∘⟨ eqϕ) ∙ sym-assoc ⟩
                ([ s.u , id ]₁ ∘ [ u , id ]₁) ∘ (ξy.ϕ ∘ v)        ≈⟨ rw (Equiv.sym Hom[-1].homomorphism) ⟩
                [ u ∘ s.u , id ]₁ ∘ (ξy.ϕ ∘ v)                    ≈⟨ skip (rw t.eqϕ) ∙ sym-assoc ∙ (sym-assoc ⟩∘⟨refl) ∙ assoc ⟩
                ([ u ∘ s.u , id ]₁ ∘ [ t.u , id ]₁) ∘ (ξy'.ϕ ∘ v) ≈⟨ rw (Equiv.sym Hom[-1].homomorphism) ⟩
                [ t.u ∘ u ∘ s.u , id ]₁ ∘ (ξy'.ϕ ∘ v)             ∎
          in (u' , (eqf' , eqϕ')) }
  ; cong = λ { {p} {q} p≈q → skip (rw p≈q) }
  } }
  ; identity = λ { {(x , y)} {p} {q} p≈q →
      let u  = proj₁ p
          u' = proj₁ q
      in begin
        id ∘ u ∘ id  ≈⟨ identityˡʳ ⟩
        u            ≈⟨ p≈q ⟩
        u'           ∎ }
  ; homomorphism = λ { {(x , y)} {(x' , y')} {(x'' , y'')} {(s , t)} {(s' , t')} {p} {q} p≈q →
      let module s  = iMR2ᴸ⇒ s
          module t  = iMR2ᴸ⇒ t
          module s' = iMR2ᴸ⇒ s'
          module t' = iMR2ᴸ⇒ t'
          u  = proj₁ p
          u' = proj₁ q
      in begin
        (t'.u ∘ t.u) ∘ (u ∘ (s.u ∘ s'.u))  ≈⟨ skip (rw p≈q) ∙ assoc ⟩
        t'.u ∘ (t.u ∘ (u' ∘ (s.u ∘ s'.u))) ≈⟨ skip (skip sym-assoc ∙ sym-assoc) ⟩
        t'.u ∘ ((t.u ∘ (u' ∘ s.u)) ∘ s'.u) ∎ }
  ; F-resp-≈ = λ { (s≈s' , t≈t') p≈q → replace-3 t≈t' p≈q s≈s' }
  }
