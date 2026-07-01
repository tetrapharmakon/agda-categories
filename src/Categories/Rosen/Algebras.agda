{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)

open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Adjoint using (Radjunct)
module Categories.Rosen.Algebras {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) (Cl : Closed M) (BC : BinaryCoproducts C) where

private
  module 𝒞 = Category C

open 𝒞
-- import Reason
-- open Reason C

import Categories.Morphism.Reasoning as MR

open HomReasoning
open MR C

open Monoidal M using (_⊗-;unit;_⊗₀_;_⊗₁_)
open BinaryCoproducts BC
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Fibred Cl using (iMR2ᴿ;iMR2ᴿ₀;iMR2ᴿ⇒)
open import Categories.Rosen.FibreA Cl using (totalAtA;_∣_)

private
  unit+- : Functor C C
  unit+- = record
    { F₀ = λ X → unit + X
    ; F₁ = λ {X} {Y} f → [ i₁ , i₂ {B = Y} ∘ f ]
    ; identity = Equiv.trans ([]-cong₂ Equiv.refl identityʳ) +-η
    ; homomorphism = +-unique (Equiv.trans (pullʳ inject₁) inject₁) (Equiv.trans (pullʳ inject₂) (Equiv.trans (pullˡ inject₂) assoc))
    ; F-resp-≈ = λ eq → []-cong₂ Equiv.refl (∘-resp-≈ʳ eq)
    }

_⊗[I+_] : {A : Obj} → Functor C C
_⊗[I+_] {A} = A +- ∘F A ⊗- 

F-Algebra-Category : {A : Obj} → Category _ _ _
F-Algebra-Category {A} = F-Algebras (_⊗[I+_] {A})


to : {A : Obj} → Functor (iMR2ᴿ A) (F-Algebra-Category {A})
to {A} = record
  { F₀ = λ x → 
    let module x = iMR2ᴿ₀ x 
        -- module ϕ* = iMR2.ϕ x.ξ
    in record 
    { A = x.B ; α = [ iMR2.f x.ξ , Closed.adjoint.Radjunct {! iMR2.ϕ x.ξ !} Cl ] }
  ; F₁ = {!  !}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }
  
{-
  record
  { F₀ = λ {(B ∣ ξ) → record { A = B ; α = [ MR2.f ξ , {!   !} ] ∘ {! Functor.F₁ (-+ (A ⊗₀ B)) ∘ ?  !} }}
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }

from : {A : Obj} → Functor (F-Algebra-Category {A}) (totalAtA A) 
from = record
  { F₀ = {!   !}
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }



AlgA≣MRS^A : {A : Obj} → StrongEquivalence (totalAtA A) (F-Algebra-Category {A})
AlgA≣MRS^A {A} = record 
  { F = to 
  ; G = from 
  ; weak-inverse = {!   !} 
  }

-}