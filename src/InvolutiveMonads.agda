{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core

module InvolutiveMonads {o l e} {𝓒 : Category o l e} where

open import Level

open import Categories.Monad hiding (id)
open import Categories.NaturalTransformation.Dinatural renaming (DinaturalTransformation to Dinat)
open import Categories.Category.Product
open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism.Reasoning as MR

open import BetterReasoning 𝓒
open Chain

open import Contramonads

open import Categories.Category.Equivalence using (WeakInverse)
open import Categories.Category.Construction.Kleisli 
open import Categories.Adjoint.Construction.Kleisli

record Involution (C : Category o l e) : Set (o ⊔ l ⊔ e) where
  field
    I   : Functor (Category.op C) C
    inv : WeakInverse I (Functor.op I)

open Involution

record InvolutiveMonad : Set (o ⊔ l ⊔ e) where
 field
  M : Monad 𝓒
  klInvol : Involution (Kleisli M)

open InvolutiveMonad

Contra→Invol : (R : Contramonad) → InvolutiveMonad
Contra→Invol R = record 
  { M = 𝐏Monad {R = R}
  ; klInvol = record 
    { I = record
      { F₀ = λ x → x
      ; F₁ = λ { {B} {A} f → {!   !} ∘ R.̂η B }
      ; identity = {!   !}
      ; homomorphism = {!   !}
      ; F-resp-≈ = {!   !}
      } 
    ; inv = {!   !} 
    } 
  } where module R = Contramonad R

Invol→Contra : (𝓘𝓥 : InvolutiveMonad) → Contramonad 
Invol→Contra 𝓘𝓥 = record
  { F = {!   !} -- Functor.op (Free (M 𝓘𝓥)) ∘F I klInvol 𝓘𝓥 ∘F Forgetful (M 𝓘𝓥) 
  ; ι = {!   !} 
  ; δ = {!   !} 
  ; C1 = {!   !} 
  ; C2 = {!   !} 
  ; C3 = {!   !} 
  ; C4 = {!   !} 
  } where 𝐈 = Functor.op (I (klInvol 𝓘𝓥))