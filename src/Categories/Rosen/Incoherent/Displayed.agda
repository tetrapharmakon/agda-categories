{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Incoherent.Displayed {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Displayed incoherent (M,R)-systems: the fibre over a fixed codomain B.
-- Reindexing along v : B ⇒ B' is *pro*functorial in B (hence a displayed category).

open import Data.Product using (Σ;_,_; proj₁; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.Rosen.Incoherent.Core Cl

import Reason
open Reason C
open Closed Cl using ([-,-]; [_,_]₁)
open HomReasoning
open MR

-- iMR2ᴸ₀: object of the left-fibre over B: a domain A plus an iMR2 A B.
record iMR2ᴸ₀ (B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A : Obj
    ξ : iMR2 A B 

-- iMR2ᴸ⇒: morphisms in the left-fibre over B: u : X.A ⇒ Y.A compatible with f and Φ.
record iMR2ᴸ⇒ {B : Obj} (X Y : iMR2ᴸ₀ B) : Set (o ⊔ ℓ ⊔ e) where
  module X = iMR2ᴸ₀ X
  module Y = iMR2ᴸ₀ Y   
  module ξX = iMR2 X.ξ  
  module ξY = iMR2 Y.ξ
  field
    u : X.A ⇒ Y.A
    eqf : ξX.f ≈ ξY.f ∘ u
    eqΦ : ξX.Φ ≈ [ u , id ]₁ ∘ ξY.Φ

-- iMR2ᴸ B: the left-fibre category over B (fibre over the codomain).
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
    ; eqΦ = Equiv.sym (cancel (Functor.identity [-,-])) 
    }
  ; _∘_ = λ p q → 
    let module p = iMR2ᴸ⇒ p 
        module q = iMR2ᴸ⇒ q
    in record 
      { u = p.u ∘ q.u 
      ; eqf = q.eqf ∙ rw-1-2 p.eqf 
      ; eqΦ = let module Hom = Functor [-,-]
                  module Hom[1-] {A} = Functor (appˡ [-,-] A)
                  module Hom[-1] {A} = Functor (appʳ [-,-] A) 
              in Equiv.sym (begin [ p.u ∘ q.u , id ]₁ ∘ p.ξY.Φ ≈⟨ pushˡ C Hom[-1].homomorphism ⟩ 
                                  [ q.u , id ]₁ ∘ [ p.u , id ]₁ ∘ p.ξY.Φ ≈⟨ Equiv.sym (refl⟩∘⟨ p.eqΦ) ⟩ 
                                  [ q.u , id ]₁ ∘ q.ξY.Φ ≈⟨ Equiv.sym q.eqΦ ⟩ 
                                  q.ξX.Φ ∎)
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

-- MRSdisplay v: bifunctor (iMR2ᴸ B)^op × iMR2ᴸ B' → Setoids,
-- capturing the *pro*functorial structure in the codomain parameter.
MRSdisplay : (v : B ⇒ B') → Bifunctor (Category.op (iMR2ᴸ B)) (iMR2ᴸ B') (Setoids (ℓ ⊔ e) e)
MRSdisplay v = record
  { F₀ = λ {(x , y) → 
     let module x  = iMR2ᴸ₀ x 
         module ξx = iMR2 x.ξ
         module y  = iMR2ᴸ₀ y 
         module ξy = iMR2 y.ξ
     in record
       { Carrier = Σ (x.A ⇒ y.A) (λ u →
           (v ∘ ξx.f ≈ ξy.f ∘ u)
         × ([ id , v ]₁ ∘ ξx.Φ ≈ [ u , id ]₁ ∘ ξy.Φ ∘ v))
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
      { _⟨$⟩_ = λ { (u , (eqf , eqΦ)) →
          let u' : x'.A ⇒ y'.A
              u' = t.u ∘ u ∘ s.u
              eqf' : v ∘ ξx'.f ≈ ξy'.f ∘ u'
              eqf' = begin
                v ∘ ξx'.f                   ≈⟨ (refl⟩∘⟨ s.eqf) ∙ sym-assoc ⟩
                (v ∘ ξx.f) ∘ s.u            ≈⟨ rw eqf ∙ assoc ⟩
                ξy.f ∘ (u ∘ s.u)            ≈⟨ rw t.eqf ∙ assoc ⟩
                ξy'.f ∘ (t.u ∘ (u ∘ s.u))   ∎
              eqΦ' : [ id , v ]₁ ∘ ξx'.Φ ≈ [ u' , id ]₁ ∘ ξy'.Φ ∘ v
              eqΦ' = begin
                [ id , v ]₁ ∘ ξx'.Φ                               ≈⟨ (refl⟩∘⟨ s.eqΦ) ∙ sym-assoc ⟩
                ([ id , v ]₁ ∘ [ s.u , id ]₁) ∘ ξx.Φ              ≈⟨ (rw [ [-,-] ]-commute) ∙ assoc ⟩
                [ s.u , id ]₁ ∘ ([ id , v ]₁ ∘ ξx.Φ)              ≈⟨ (refl⟩∘⟨ eqΦ) ∙ sym-assoc ⟩
                ([ s.u , id ]₁ ∘ [ u , id ]₁) ∘ (ξy.Φ ∘ v)        ≈⟨ rw (Equiv.sym Hom[-1].homomorphism) ⟩
                [ u ∘ s.u , id ]₁ ∘ (ξy.Φ ∘ v)                    ≈⟨ skip (rw t.eqΦ) ∙ sym-assoc ∙ (sym-assoc ⟩∘⟨refl) ∙ assoc ⟩
                ([ u ∘ s.u , id ]₁ ∘ [ t.u , id ]₁) ∘ (ξy'.Φ ∘ v) ≈⟨ rw (Equiv.sym Hom[-1].homomorphism) ⟩
                [ t.u ∘ u ∘ s.u , id ]₁ ∘ (ξy'.Φ ∘ v)             ∎
          in (u' , (eqf' , eqΦ')) }
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
