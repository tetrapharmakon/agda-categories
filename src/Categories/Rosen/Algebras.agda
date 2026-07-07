{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
-- this module has to assume that the ambient category is *symmetric* monoidal; the definition of the endofunctor is agnostic about preservation of coproducts by ⊗ ... 
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Functor using (Functor; _∘F_)

open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Adjoint using (Adjoint)
module Categories.Rosen.Algebras {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) (Cl : Closed M) (S : Symmetric M) (BC : BinaryCoproducts C) where

-- Incoherent (M,R)-systems as endofunctor algebras.
-- The endofunctor X ↦ A ⊗ (𝟙 + X) (conceptually; implemented via
-- distributivity as A + (A ⊗ X)) captures a certain class of
-- (M,R)-systems.  WIP: the equivalence with iMR2ᴿ A is incomplete.

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
open Symmetric S hiding (_⊗-; unit; _⊗₀_; _⊗₁_) renaming (braided-iso to β)
open Closed Cl using (adjoint)
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Fibred Cl using (iMR2ᴿ;iMR2ᴿ₀;iMR2ᴿ⇒)
-- open import Categories.Rosen.FibreA Cl using (totalAtA;_∣_)

private
  -- unit+-: endofunctor X ↦ 𝟙 + X (coproduct with the monoidal unit).
  unit+- : Functor C C
  unit+- = record
    { F₀ = λ X → unit + X
    ; F₁ = λ {X} {Y} f → [ i₁ , i₂ {B = Y} ∘ f ]
    ; identity = Equiv.trans ([]-cong₂ Equiv.refl identityʳ) +-η
    ; homomorphism = +-unique (Equiv.trans (pullʳ inject₁) inject₁) (Equiv.trans (pullʳ inject₂) (Equiv.trans (pullˡ inject₂) assoc))
    ; F-resp-≈ = λ eq → []-cong₂ Equiv.refl (∘-resp-≈ʳ eq)
    }

-- _⊗[I+_] : endofunctor X ↦ A ⊗ (𝟙 + X) on C (conceptually).
-- The implementation uses distributivity: A ⊗ (𝟙 + X) ≅ A + (A ⊗ X).
_⊗[I+_] : {A : Obj} → Functor C C
_⊗[I+_] {A} = A +- ∘F A ⊗- 

-- Category of F-algebras for the endofunctor X ↦ A ⊗ (𝟙 + X).
F-Algebra-Category : {A : Obj} → Category _ _ _
F-Algebra-Category {A} = F-Algebras (_⊗[I+_] {A})


-- to: comparison functor from iMR2ᴿ A to F-algebras. (WIP: has holes)
to : {A : Obj} → Functor (iMR2ᴿ A) (F-Algebra-Category {A})
to {A} = record
  { F₀ = λ x → let module x = iMR2ᴿ₀ x
                   module ξ = iMR2 x.ξ
                   ϕ' = adjoint.Radjunct ξ.ϕ
               in record 
    { A = x.B ; α = [ ξ.f , ϕ' ∘ β.from ] }
  ; F₁ = λ f → 
    let module f = iMR2ᴿ⇒ f 
    in record { f = f.v ; commutes = {!  !} }
    -- commutes is the only part that is not trivial to implement; it requires a lot of yoga with mates and the braiding of C...
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ x → x
  }
  
-- WIP: the converse, from, and equivalence AlgA≣MRS^A are not yet implemented.
from : {A : Obj} → Functor (F-Algebra-Category {A}) (iMR2ᴿ A) 
from = record
  { F₀ = λ x → 
    let module x = F-Algebra x 
        α = x.α
    in record 
    { B = x.A 
    ; ξ = ⟪ α ∘ i₁ , adjoint.Ladjunct (α ∘ i₂ ∘ β.from) ⟫  
    }
  ; F₁ = λ f → 
    let module f = F-Algebra-Morphism 
        f' = f .F-Algebra-Morphism.f 
    in record 
      { v = f'
      ; eqf = pullˡ (f.commutes f) ○ assoc ○ ∘-resp-≈ʳ (Equiv.trans inject₁ identityʳ) 
      ; eqϕ = {!  !} 
      }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ z → z
  }



AlgA≣MRS^A : {A : Obj} → StrongEquivalence (iMR2ᴿ A) (F-Algebra-Category {A})
AlgA≣MRS^A {A} = record 
  { F = to {A} 
  ; G = from {A}
  ; weak-inverse = record 
    { F∘G≈id = niHelper (record 
      { η = λ X → record 
        { f = id 
        ; commutes = identityˡ ○ introʳ (Functor.identity _⊗[I+_]) ○ {!  !} ⟩∘⟨refl -- Equiv.sym (Functor.identity _⊗[I+_] ○ {!  !}) 
        } 
      ; η⁻¹ = λ X → record 
        { f = id 
        ; commutes = identityˡ ○ {!  !} 
        } 
      ; commute = λ f → Equiv.trans identityˡ (Equiv.sym identityʳ) 
      ; iso = λ X → record 
        { isoˡ = identityˡ 
        ; isoʳ = identityˡ 
        } 
      }) 
    ; G∘F≈id = niHelper (record 
      { η = λ X → record 
        { v = id 
        ; eqf = identityˡ ○ inject₁ 
        ; eqϕ = {!  !} -- (elimˡ (Functor.identity _⊗[I+_]) ○ {!  !}) ○ Equiv.sym identityʳ 
        } 
      ; η⁻¹ = {!  !} 
      ; commute = {!  !} 
      ; iso = {!  !} 
      }) 
    } 
  }
