{-# OPTIONS --without-K --safe --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level using (0ℓ; _⊔_)

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

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-poset)
open import Data.Product using (Σ;_,_;proj₁;proj₂)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Construction.Thin 0ℓ ≤-poset
open import Categories.Functor using (_∘F_) renaming (id to idF)

𝕄ℝ𝕊 : (n : ℕ) → Σ (Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e) (λ x → Functor x Arr.Arrow)
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
        in Vₙ.F₁ f.g }
      ; identity = Vₙ.identity
      ; homomorphism = Vₙ.homomorphism
      ; F-resp-≈ = λ f≈g → Vₙ.F-resp-≈ (proj₂ f≈g)
      }

𝕄ℝ𝕊ₒ : (n : ℕ) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
𝕄ℝ𝕊ₒ n = proj₁ (𝕄ℝ𝕊 n)

𝕄ℝ𝕊ₐ : (n : ℕ) → _
𝕄ℝ𝕊ₐ n = proj₂ (𝕄ℝ𝕊 n)

Π-MRS : (n : ℕ) → Functor (𝕄ℝ𝕊ₒ (suc n)) (𝕄ℝ𝕊ₒ n)
Π-MRS n = record
  { F₀ = λ x → {!  !}
  ; F₁ = {!  !}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }

pℕ : Category 0ℓ 0ℓ 0ℓ
pℕ = Thin

𝕄ℝ𝕊-down : ∀ {n m} → m ≤ n → Functor (𝕄ℝ𝕊ₒ n) (𝕄ℝ𝕊ₒ m)
𝕄ℝ𝕊-down {n} z≤n = reduce n
  where
    reduce : (k : ℕ) → Functor (𝕄ℝ𝕊ₒ k) (𝕄ℝ𝕊ₒ 0)
    reduce 0 = idF -- idF
    reduce (suc k) = reduce k ∘F Π-MRS k
𝕄ℝ𝕊-down (s≤s {m} {n} m≤n) = lift (𝕄ℝ𝕊-down m≤n)
  where
    lift : Functor (𝕄ℝ𝕊ₒ n) (𝕄ℝ𝕊ₒ m) → Functor (𝕄ℝ𝕊ₒ (suc n)) (𝕄ℝ𝕊ₒ (suc m))
    lift F = let module F' = Functor F in record
      { F₀ = λ x →
        let module x = IsoCommaObj x
        in record { a = x.a ; b = F'.F₀ x.b ; iso = {! !} }
      ; F₁ = λ { {x} {y} f →
        let module x = IsoCommaObj x
            module y = IsoCommaObj y
            module f = IsoComma⇒ f
        in record { f = f.f ; g = F'.F₁ f.g ; commute = {! !} } }
      ; identity = {!  !} -- Category.Equiv.refl ElMRS , F'.identity
      ; homomorphism = {!  !} -- Category.Equiv.refl ElMRS , F'.homomorphism
      ; F-resp-≈ = λ eq → {!  !} , F'.F-resp-≈ (proj₂ eq)
      }

MRS-chain : Functor (Category.op pℕ) (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e)
MRS-chain = record
  { F₀ = 𝕄ℝ𝕊ₒ
  ; F₁ = λ {n} {m} m≤n → 𝕄ℝ𝕊-down m≤n
  ; identity = {! !}
  ; homomorphism = {! !}
  ; F-resp-≈ = {! !}
  }

open import Categories.Diagram.Limit MRS-chain renaming (Limit to MRS-Limit)

MRS∞ = MRS-Limit.apex
MRS∞-proj = MRS-Limit.proj
MRS∞-commute = MRS-Limit.limit-commute