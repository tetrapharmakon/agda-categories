{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (_⊔_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Category.Construction.IsoComma using (IsoComma;IsoCommaObj;IsoComma⇒)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Rosen.HigherMRS {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  module 𝒞 = Category C

import Reason
open Reason C

import Categories.Morphism.Reasoning as MR

open HomReasoning
open MR

open import Categories.Functor.Profunctor.Tabulator using (tab₀;tab⇒)
open import Categories.Rosen.Core Cl
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}
open import Categories.Rosen.Tabulator Cl using (V₁; 𝕋MRS)

MRS3 : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
MRS3 = IsoComma ℝ V₁


{-

Now I want something ambitious:

1. Import Natural numbers from the standard library

2. define

-}

-- V : (n : ℕ) → Functor 

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ;_,_;proj₁;proj₂)

𝕄ℝ𝕊 : (n : ℕ) → Σ (Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e) (λ x → Functor x Arr.Arrow)
-- 𝕄ℝ𝕊 zero = 𝕋MRS , V₁ 
𝕄ℝ𝕊 zero = MRS3 , V₂
  where 
    V₂ : Functor MRS3 Arr.Arrow 
    V₂ = record
      { F₀ = λ x → 
        let module x = IsoCommaObj x 
        in record { arr = MR2.f (tab₀.ξ x.b) }
      ; F₁ = λ { {x} {y} f → 
        let module x = IsoCommaObj x 
            module y = IsoCommaObj y 
            module f = IsoComma⇒ f
        in mor⇒ {dom⇒ = tab⇒.l f.g} {cod⇒ = tab⇒.r f.g} 
          (begin _ ≈⟨ sym-id-1 ○ assoc ⟩ 
                 _ ≈⟨ proj₁ (tab⇒.eq f.g) ⟩ 
                 _ ≈⟨ id-0 ⟩ 
                 _ ∎)}
      ; identity = Equiv.refl , Equiv.refl
      ; homomorphism = Equiv.refl , Equiv.refl
      ; F-resp-≈ = λ {(_ , dat) → (dat .proj₁) , (dat .proj₂)}
      }
𝕄ℝ𝕊 (suc n) 
  = let MRSn = proj₂ (𝕄ℝ𝕊 n) 
        module Vₙ = Functor MRSn
    in IsoComma ℝ MRSn
  , record
      { F₀ = λ x → 
        let module x = IsoCommaObj x
        in Vₙ.F₀ x.b
      ; F₁ = λ { {x} {y} f → 
        let module x = IsoCommaObj x 
            module y = IsoCommaObj y 
            module f = IsoComma⇒ f
        in Vₙ.F₁ f.g } --  mor⇒ {dom⇒ = {! Morphism⇒.dom⇒ (Vₙ.F₁ f.g)  !}} {cod⇒ = {!  !}} {!  !}  }
      ; identity = Vₙ.identity
      ; homomorphism = Vₙ.homomorphism
      ; F-resp-≈ = λ f≈g → Vₙ.F-resp-≈ (proj₂ f≈g)
      }

𝕄ℝ𝕊ₒ : (n : ℕ) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
𝕄ℝ𝕊ₒ n = proj₁ (𝕄ℝ𝕊 n)

𝕄ℝ𝕊ₐ : (n : ℕ) → _ -- (n : ℕ) → 
𝕄ℝ𝕊ₐ n = proj₂ (𝕄ℝ𝕊 n)

Π-MRS : (n : ℕ) → Functor (𝕄ℝ𝕊ₒ (suc n)) (𝕄ℝ𝕊ₒ n)
Π-MRS n = record
  { F₀ = λ x → {!  !}
  ; F₁ = {!  !}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }

{-
use Categories.Category.Construction.Thin
to instantiate the category pℕ as the poset of natural numbers 
seen as category.

Then define a (contravariant) functor from pℕ into the category of categories
Categories.Category.Instance.Cats 
sending n to 𝕄ℝ𝕊ₒ n and an inequality n ≤ n+1 to the functor Π-MRS
 -}