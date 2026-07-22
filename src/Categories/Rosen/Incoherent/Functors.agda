{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

-- open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Rosen.Incoherent.Functors {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

-- Incoherent (M,R)-systems: a simple diagram A —f→ B —Φ→ [A,B]
-- without the natural transformation condition of full MR2.

open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor;_∘F_)
open import Categories.Functor.Bifunctor using (appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute;[_]-decompose₁;[_]-decompose₂)
open import Categories.Morphism.Reasoning as MR

import Reason
open Reason C
open Closed Cl using (adjoint; mate;[-,-]; [_,_]₀; [_,_]₁;⊗;_⊗₀_;_⊗₁_;_⊗-;-⊗_)
open HomReasoning
open MR

-- open Symmetric S hiding (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_) renaming (braided-iso to β)
-- module Arr = Categories.Category.Construction.Arrow C

open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Elements Cl

module _ {X Y : iMR2₀} (f : twiMR2⇒ X Y) where
  module X = iMR2₀ X
  ΦX = iMR2.Φ X.ξ 
  ΦX* = adjoint.Radjunct ΦX
  module Y = iMR2₀ Y
  ΦY = iMR2.Φ Y.ξ 
  ΦY* = adjoint.Radjunct ΦY
  module F = twiMR2⇒ f
  ε = adjoint.counit.η

  lemma-epsilon :
    F.r ∘ ε X.B ∘ id {[ F.X.A , F.X.B ]₀} ⊗₁ F.l ≈ ε Y.B ∘ [ F.l , F.r ]₁ ⊗₁ id {F.Y.A}
  lemma-epsilon = 
    begin F.r ∘ ε X.B ∘ id {[ F.X.A , F.X.B ]₀} ⊗₁ F.l 
      ≈⟨ pullˡ C (adjoint.counit.sym-commute F.r) ∙ assoc ⟩
          ε Y.B ∘ Functor.F₁ ((-⊗ F.X.A) ∘F appˡ [-,-] F.X.A) F.r ∘ id {[ F.X.A , F.X.B ]₀} ⊗₁ F.l 
      ≈⟨ (refl⟩∘⟨ Equiv.sym [ ⊗ ]-commute) ⟩
          ε Y.B ∘ id {[ F.X.A , F.Y.B ]₀} ⊗₁ F.l ∘ [ id {F.X.A} , F.r ]₁ ⊗₁ id {F.Y.A} 
      ≈⟨ pullˡ C (Equiv.sym (mate.commute₂ F.l {F.Y.B})) ⟩
          (ε Y.B ∘ [ F.l , id {F.Y.B} ]₁ ⊗₁ id {F.Y.A}) ∘ [ id {F.X.A} , F.r ]₁ ⊗₁ id {F.Y.A} 
      ≈⟨ assoc ⟩
          ε Y.B ∘ [ F.l , id {F.Y.B} ]₁ ⊗₁ id {F.Y.A} ∘ [ id {F.X.A} , F.r ]₁ ⊗₁ id {F.Y.A} 
      ≈˘⟨ refl⟩∘⟨ Functor.homomorphism (appʳ ⊗ F.Y.A) ⟩
          ε Y.B ∘ ([ F.l , id {F.Y.B} ]₁ ∘ [ id {F.X.A} , F.r ]₁) ⊗₁ id {F.Y.A}  
      ≈˘⟨ refl⟩∘⟨ Functor.F-resp-≈ (appʳ ⊗ F.Y.A) [ [-,-] ]-decompose₁ ⟩ 
          ε Y.B ∘ [ F.l , F.r ]₁ ⊗₁ id {F.Y.A} ∎ 

  lemma-delta :
    [ F.l , F.r ]₁ ∘ adjoint.Ladjunct (ΦX* ∘ (ε X.B ⊗₁ id)) ∘ id {[ F.X.A , F.X.B ]₀} ⊗₁ F.l
      ≈
    adjoint.Ladjunct (ΦY* ∘ (ε Y.B ⊗₁ id)) ∘ [ F.l , F.r ]₁ ⊗₁ id {F.Y.A}
  lemma-delta = 
    begin [ F.l , F.r ]₁ ∘ adjoint.Ladjunct (ΦX* ∘ ε F.X.B ⊗₁ id) ∘ id ⊗₁ F.l 
      ≈⟨ refl⟩∘⟨ (adjoint.Ladjunct-comm′ ∙ ((adjoint.LRadjunct≈id ⟩∘⟨refl)) ⟩∘⟨refl) ⟩ 
          [ F.l , F.r ]₁ ∘ (ΦX ∘ ε F.X.B) ∘ id ⊗₁ F.l 
      ≈⟨ refl⟩∘⟨ pullʳ C (Equiv.sym (mate.commute₂ F.l)) ⟩ 
          [ F.l , F.r ]₁ ∘ ΦX ∘ ε F.X.B ∘ ([ F.l , id ]₁ ⊗₁ id) 
      ≈⟨ refl⟩∘⟨ pullˡ C (adjoint.counit.sym-commute F.ξX.Φ) ⟩ 
          [ F.l , F.r ]₁ ∘ (ε _ ∘ [ id {F.Y.A} , F.ξX.Φ ]₁ ⊗₁ id) ∘ ([ F.l , id ]₁ ⊗₁ id) 
      ≈⟨ sym-assoc ∙ (pullˡ C (adjoint.counit.sym-commute _) ⟩∘⟨refl) ⟩
          ((ε _ ∘ [ id , [ F.l , F.r ]₁ ]₁ ⊗₁ id) ∘ [ id , F.ξX.Φ ]₁ ⊗₁ id) ∘ [ F.l , id ]₁ ⊗₁ id 
          -- ((f ∘ g) ∘ h) ∘ i 
      ≈⟨ anti-assoc-4 ∙ (refl⟩∘⟨ Equiv.sym ((Functor.homomorphism (appʳ ⊗ F.Y.A) ○ refl⟩∘⟨ Functor.homomorphism (appʳ ⊗ F.Y.A)))) ⟩
          ε _ ∘ ([ id , [ F.l , F.r ]₁ ]₁ ∘ [ id , ΦX ]₁ ∘ [ F.l , id ]₁) ⊗₁ id {F.Y.A} 
      ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ (appʳ ⊗ F.Y.A) (pullˡ C (Equiv.sym (Functor.homomorphism (appˡ [-,-] F.Y.A)))) ⟩
          ε _ ∘ ([ id , [ F.l , F.r ]₁ ∘ ΦX ]₁ ∘ [ F.l , id ]₁) ⊗₁ id {F.Y.A} 
      ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ (appʳ ⊗ F.Y.A) (Functor.F-resp-≈ (appˡ [-,-] F.Y.A) (sym F.eqΦ) ⟩∘⟨refl) ⟩
          ε _ ∘ ([ id , ΦY ∘ F.r ]₁ ∘ [ F.l , id ]₁) ⊗₁ id {F.Y.A} 
      ≈⟨ {!   !} ⟩
          {!   !}
          (ΦY ∘ ε F.Y.B) ∘ [ F.l , F.r ]₁ ⊗₁ id 
      ≈˘⟨ (adjoint.LRadjunct≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
          ((adjoint.Ladjunct ΦY*) ∘ ε F.Y.B) ∘ [ F.l , F.r ]₁ ⊗₁ id 
      ≈˘⟨ adjoint.Ladjunct-comm′ ⟩∘⟨refl ⟩
          adjoint.Ladjunct (ΦY* ∘ ε F.Y.B ⊗₁ id) ∘ [ F.l , F.r ]₁ ⊗₁ id ∎

[_]f : Functor τ[iMR2] Arr.Arrow 
[_]f = record
  { F₀ = λ x → let module x = iMR2₀ x in record { dom = x.A ; cod = x.B ; arr = iMR2.f x.ξ }
  ; F₁ = λ f → let module f = iMR2⇒ f in mor⇒ f.eqf
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x
  }

open import Categories.Rosen.Incoherent.Repairs Cl

[_]Φ : Functor τ[iMR2] irepairs
[_]Φ = record
  { F₀ = λ x → let module x = iMR2₀ x in record 
    { A = x.A 
    ; B = x.B 
    ; Φ = iMR2.Φ x.ξ 
    }
  ; F₁ = λ f → let module f = iMR2⇒ f in record 
    { u = f.l
    ; v = f.r
    ; eq = f.eqΦ
    }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ z → z .proj₁
  }


open import Categories.Rosen.Incoherent.Mealy Cl

Arbib : Functor τ'[iMR2] totalMealy
Arbib = record
  { F₀ = λ x → 
    let module x = iMR2₀ x 
        module ξX = iMR2 x.ξ
        Φ* = adjoint.Radjunct ξX.Φ
    in record 
    { A = x.A 
    ; B = x.B 
    ; m = record 
      { E = [ x.A , x.B ]₀ 
      ; d = adjoint.Ladjunct (Φ* ∘ (adjoint.counit.η x.B ⊗₁ id)) 
      ; s = adjoint.counit.η x.B 
      } 
    }
  ; F₁ = λ f → 
    let module f = twiMR2⇒ f 
        module AX = adjoint {f.X.A}
        module AY = adjoint {f.Y.A}
        εXB = AX.counit.η f.X.B
        εYB = AY.counit.η f.Y.B
    in record 
      { l = f.l
      ; r = f.r 
      ; u = [ f.l , f.r ]₁ 
      ; d-eq = lemma-delta f 
      ; s-eq = lemma-epsilon f 
      }
  ; identity = refl , refl , [-,-].identity
  ; homomorphism = refl , refl , [-,-].homomorphism
  ; F-resp-≈ = λ z → z .proj₁ , z .proj₁ , [-,-].F-resp-≈ z
  }
