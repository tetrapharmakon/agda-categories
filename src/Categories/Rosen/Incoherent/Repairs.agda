{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.Incoherent.Repairs {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —ϕ→ [A,B]
-- without the natural transformation condition of full MR2.

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using ([-,-];[_,-];[-,_];[_,_]₀; [_,_]₁)
open HomReasoning
open MR

-- module Arr = Categories.Category.Construction.Arrow C

open import Categories.Rosen.Incoherent.Core Cl


-- Objects of the incoherent repair fibration: objects A,B and a morphism ϕ : B ⇒ [A,B].
record irep₀ : Set (o ⊔ ℓ ⊔ e) where
  field
    A : Obj
    B : Obj
    ϕ : B ⇒ [ A , B ]₀

-- Morphisms of the repair fibration: u : X.A ⇒ Y.A such that
-- (nHom u ∘ʳ Cod) ∘ᵥ Y.ϕ ≃ X.ϕ.
record irep⇒ (X Y : irep₀) : Set (o ⊔ ℓ ⊔ e) where
  module X = irep₀ X
  module Y = irep₀ Y
  field
    u : X.A ⇒ Y.A
    v : X.B ⇒ Y.B
    eq : [ u , id ]₁ ∘ Y.ϕ ∘ v ≈ [ id , v ]₁ ∘ X.ϕ

-- The category of repairs: the total category of the fibration.
irepairs : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
irepairs = record
  { Obj = irep₀
  ; _⇒_ = λ s t → irep⇒ s t
  ; _≈_ = λ f g →
    let module f = irep⇒ f
        module g = irep⇒ g
    in f.u ≈ g.u
  ; id = record { u = id ; v = id
       ; eq = id-2 }
  ; _∘_ = λ f g →
    let module f = irep⇒ f
        module g = irep⇒ g
    in record { u = f.u ∘ g.u ; v = f.v ∘ g.v 
         ; eq = begin [ f.u ∘ g.u , id ]₁ ∘ f.Y.ϕ ∘ f.v ∘ g.v ≈⟨ Functor.homomorphism ([-, _ ]) ⟩∘⟨refl ⟩ 
                      ([ g.u , id ]₁ ∘ [ f.u , id ]₁ ) ∘ f.Y.ϕ ∘ f.v ∘ g.v ≈⟨ (refl⟩∘⟨ sym-assoc) ○ assoc ○ (refl⟩∘⟨ sym-assoc) ○ refl⟩∘⟨ (f.eq ⟩∘⟨refl ) ⟩ 
                      [ g.u , id ]₁ ∘ ([ id , f.v ]₁ ∘ g.Y.ϕ) ∘ g.v ≈⟨ refl⟩∘⟨ assoc ○ pullˡ C ((Equiv.sym [ [-,-] ]-commute)) ⟩ 
                      ([ id , f.v ]₁ ∘ [ g.u , id ]₁) ∘ g.Y.ϕ ∘ g.v ≈⟨ pullʳ C (g.eq) ⟩
                      [ id , f.v ]₁ ∘ [ id , g.v ]₁ ∘ g.X.ϕ ≈⟨ pullˡ C (Equiv.sym (Functor.homomorphism [ _ ,-])) ⟩
                      [ id , f.v ∘ g.v ]₁ ∘ g.X.ϕ ∎ }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
