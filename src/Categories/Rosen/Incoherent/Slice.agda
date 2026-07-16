{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (_⊔_)
open import Categories.Category using (Category)
-- open import Categories.Category.Cartesian using (BinaryProducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Rosen.Incoherent.Slice
  {o ℓ e} {C : Category o ℓ e}
  (M : Monoidal C)
  (Cl : Closed M)
  (S : Symmetric M)
  (BC : BinaryProducts C)
  where

open import Categories.Category.BinaryProducts using (BinaryProducts)
----------------------------------------------------------------------
-- Incoherent (M,R)-Systems as Algebras
--
-- Fix an object B... (todo)
----------------------------------------------------------------------

open Category C

open import Data.Product using (_,_)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Displayed Cl using (iMR2ᴸ; iMR2ᴸ₀; iMR2ᴸ⇒)

open import Categories.Category.Slice using (Slice)


open HomReasoning
open MR C
open Monoidal M using (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_)
open BinaryProducts BC


I+ : Functor C C 
I+ = -+ unit 

open Symmetric S hiding (_⊗-; -⊗_; unit; _⊗₀_; _⊗₁_) renaming (braided-iso to β)
open Closed Cl using (adjoint; [_,_]₀; [_,_]₁; [_,-])

slice : {B : Obj} → Category (o ⊔ ℓ) (ℓ ⊔ e) e
slice {B} = Slice ([ unit , B ]₀ × [ B , B ]₀)



to : {B : Obj} → Functor (iMR2ᴸ B) (slice {B})
to {B} = record
  { F₀ = λ x → let module x = iMR2ᴸ₀ x in {!  iMR2.ϕ x.ξ !}
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }
  
-- Converse functor slice → iMR2ᴸ B.
from : {B : Obj} → Functor (slice {B}) (iMR2ᴸ B) 
from {B} = {!   !}

------------------------------------------------------------------------
-- Equivalence
------------------------------------------------------------------------

AlgA≣MRS-B : {B : Obj} → StrongEquivalence (iMR2ᴸ B) (slice {B})
AlgA≣MRS-B {B} = record 
  { F = to 
  ; G = from 
  ; weak-inverse = record 
    { F∘G≈id = niHelper (record 
      { η = {!   !} 
      ; η⁻¹ = {!   !} 
      ; commute = {!   !} 
      ; iso = {!   !} }) 
    ; G∘F≈id = niHelper (record 
      { η = {!   !} 
      ; η⁻¹ = {!   !} 
      ; commute = {!   !} 
      ; iso = {!   !} }) 
    } 
  }