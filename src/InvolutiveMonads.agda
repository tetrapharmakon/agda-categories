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

record Involution {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    I   : Functor (Category.op C) C
    inv : WeakInverse I (Functor.op I)

record InvolutiveMonad : Set (o ⊔ l ⊔ e) where
 field
  M : Monad 𝓒
  klInvol : Involution (Kleisli M)