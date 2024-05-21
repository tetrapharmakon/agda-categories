{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Core

module Contramonads {o l e} {𝓒 : Category o l e} where

open import Level

open import Categories.Monad hiding (id)
open import Categories.NaturalTransformation.Dinatural
open import Categories.Category.Product
open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism.Reasoning as MR

module 𝓒 = Category 𝓒
open 𝓒

private
 variable
  o' l' e' : Level 
  𝓓 : Category o' l' e'

_ᵒ×_ : (𝓐 : Category o l e) → (𝓑 : Category o' l' e') → Category (o ⊔ o') (l ⊔ l') (e ⊔ e')
𝓐 ᵒ× 𝓑 = Product (Category.op 𝓐) 𝓑

liftF⁻ : Functor 𝓒 𝓓 → Functor (𝓒 ᵒ× 𝓒) 𝓓 
liftF⁻ F = F ∘F πʳ

liftF⁺ : Functor (Category.op 𝓒) 𝓓 → Functor (𝓒 ᵒ× 𝓒) 𝓓 
liftF⁺ F = F ∘F πˡ

record Contramonad : Set (o ⊔ l ⊔ e) where
 field
  F : Functor (Category.op 𝓒) 𝓒
  ι : DinaturalTransformation (liftF⁻ idF) (liftF⁺ F)
 
 F² = F ∘F Functor.op F

 field
  δ : DinaturalTransformation (liftF⁺ F) (liftF⁻ F²)

 module F = Functor F
 module ι = DinaturalTransformation ι
 module δ = DinaturalTransformation δ
 module F² = Functor F²
 
 field
  C1 : ∀ {A B : Obj} {f : A ⇒ B} → F².F₁ f ∘ δ.α A ∘ ι.α A ≈ δ.α B ∘ ι.α B ∘ f
  C2 : ∀ {A B : Obj} {f : A ⇒ B} → F².F₁ f ∘ δ.α A ≈ δ.α B ∘ F.F₁ (ι.α B) ∘ F².F₁ f ∘ δ.α A
  C3 : ∀ {A : Obj} → id ≈ F.F₁ (ι.α A) ∘ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ∘ ι.α (F.F₀ A)
  C4 : ∀ {A : Obj} → F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ≈ δ.α A ∘ F.F₁ (ι.α A) ∘ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A)

 ̂η : ∀ {X : Obj} → X ⇒ F².F₀ X  
 ̂η {X} = δ.α X ∘ ι.α X

 𝐏 : ∀ {A B : Obj} (f : A ⇒ B) → F.F₀ A ⇒ F.F₀ B 
 𝐏 {A} {B} f = F.F₁ (ι.α B) ∘ F².F₁ f ∘ δ.α A

 ̂μ : ∀ {X : Obj} → F².F₀ X ⇒ F.F₀ X
 ̂μ {X} = F.F₁ (ι.α X) ∘ F.F₁ (δ.α X) ∘ δ.α (F.F₀ X)

 C5 : ∀ {A B : Obj} (f : A ⇒ B) → F.F₁ (δ.α A) ∘ F.F₁ (F².F₁ f) ≈ F.F₁ (δ.α A) ∘ F.F₁ (F².F₁ f) ∘ F².F₁ (ι.α B) ∘ F.F₁ (δ.α B)
 C5 f = {!    !} 
   where open 𝓒.HomReasoning
         open MR 𝓒

 C6 : ∀ {X : Obj} → F.F₁ (ι.α X) ∘ δ.α X ≈ id
 C6 {X} = {!   !}
 C7 : ∀ {X : Obj} → F.F₁ (δ.α X) ∘ ̂η {F.F₀ X} ≈ δ.α X
 C7 {X} = {!   !} 
 C8 : ∀ {X : Obj} → F.F₁ (̂η {F.F₀ X}) ∘ F².F₁ (δ.α X) ≈ F.F₁ (δ.α X)
 C8 {X} = {!   !} 

 𝐏-unit-lemma : ∀ {A : Obj} → δ.α A ≈ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ∘ ι.α (F.F₀ A)
 𝐏-unit-lemma = let open 𝓒.HomReasoning
                    open MR 𝓒 in begin {!   !} ≈˘⟨ identityʳ ⟩
                                       {!   !} ≈⟨ (refl⟩∘⟨ C3) ⟩
                                       {!   !} ≈⟨ {!   !} ⟩
                                       {!   !} ∎

open Contramonad

F²Monad : (R : Contramonad) → Monad 𝓒 
F²Monad R = record
  { F = F² R
  ; η = ntHelper (record 
    { η = λ X → ̂η R {X} 
    ; commute = {!   !} 
    })
  ; μ = ntHelper (record 
    { η = λ X → F₁ (F R) (δ.α R (F₀ (F R) X) ∘ ι.α R (F₀ (F R) X)) 
    ; commute = {!   !} 
    })
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  } where module R = Contramonad R
          open Functor

𝐏Monad : (R : Contramonad) → Monad 𝓒 
𝐏Monad R = record
  { F = record
    { F₀ = λ X → F₀ R.F X
    ; F₁ = λ f → R.𝐏 f
    ; identity = λ { {A} → elim-center (identity (F² R)) ○ {!   !} } -- F.F₁ (ι.α A)
    ; homomorphism = λ { {X} {Y} {Z} {f} {g} → {!   !}}
    ; F-resp-≈ = λ f≈g → refl⟩∘⟨ (F-resp-≈ R.F² f≈g ⟩∘⟨refl)
    }
  ; η = {!   !}
  ; μ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  } where module R = Contramonad R
          open Functor
          open 𝓒.HomReasoning
          open MR 𝓒