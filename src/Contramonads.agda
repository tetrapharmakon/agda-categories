{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core

module Contramonads {o l e} {𝓒 : Category o l e} where

open import Level

open import Categories.Monad hiding (id)
open import Categories.NaturalTransformation.Dinatural renaming (DinaturalTransformation to Dinat)
open import Categories.Category.Product
open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism.Reasoning as MR

open import BetterReasoning 𝓒
open Chain

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

open Dinat

antiCommute⁻⁺ : {H : Functor 𝓒 𝓒} {G : Functor (Category.op 𝓒) 𝓒} (θ : Dinat (liftF⁻ H) (liftF⁺ G)) →
 ∀ {A B} {f : A ⇒ B} → Functor.F₁ G f ∘ α θ B ∘ Functor.F₁ H f ≈ α θ A
antiCommute⁻⁺ {H} {G} θ {A} {B} {f} = 
  Equiv.sym (commute θ f) ∙ 
  MR.elimˡ 𝓒 (identity G) ∙ 
  MR.elimʳ 𝓒 (identity H)
  where open Functor

antiCommute⁺⁻ : {G : Functor 𝓒 𝓒} {H : Functor (Category.op 𝓒) 𝓒} (θ : Dinat (liftF⁺ H) (liftF⁻ G)) →
 ∀ {A B} {f : A ⇒ B} → Functor.F₁ G f ∘ α θ A ∘ Functor.F₁ H f ≈ α θ B
antiCommute⁺⁻ {G} {H} θ {A} {B} {f} = 
  commute θ f ∙ 
  (MR.elimˡ 𝓒 (identity G) ∙ 
  MR.elimʳ 𝓒 (identity H))
  where open Functor

record Contramonad : Set (o ⊔ l ⊔ e) where
 field
  F : Functor (Category.op 𝓒) 𝓒
  ι : Dinat (liftF⁻ idF) (liftF⁺ F)

 F² = F ∘F Functor.op F

 field
  δ : Dinat (liftF⁺ F) (liftF⁻ F²)

 module F = Functor F
 module ι = Dinat ι
 module δ = Dinat δ
 module F² = Functor F²

 field
  C1 : ∀ {A B : Obj} {f : A ⇒ B} →
   (δ.α B ∘ ι.α B) ∘ f ≈ F².F₁ f ∘ δ.α A ∘ ι.α A
  C2 : ∀ {A B : Obj} {f : A ⇒ B} →
   F².F₁ f ∘ δ.α A ≈ δ.α B ∘ F.F₁ (ι.α B) ∘ F².F₁ f ∘ δ.α A
  C3 : ∀ {A : Obj} →
   id ≈ F.F₁ (ι.α A) ∘ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ∘ ι.α (F.F₀ A)
  C4 : ∀ {A : Obj} →
   F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ≈ δ.α A ∘ F.F₁ (ι.α A) ∘ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A)

 ̂η : ∀ (X : Obj) → X ⇒ F².F₀ X
 ̂η X = δ.α X ∘ ι.α X

 𝐏 : ∀ {A B : Obj} (f : A ⇒ B) → F.F₀ A ⇒ F.F₀ B
 𝐏 {A} {B} f = F.F₁ (ι.α B) ∘ F².F₁ f ∘ δ.α A

 ̂μ : ∀ {X : Obj} → F².F₀ X ⇒ F.F₀ X
 ̂μ {X} = F.F₁ (ι.α X) ∘ F.F₁ (δ.α X) ∘ δ.α (F.F₀ X)

 module _ where
  open Functor

  C5 : ∀ {A B : Obj} (f : A ⇒ B) →
   F.F₁ (δ.α A) ∘ F.F₁ (F².F₁ f) ≈ F.F₁ (δ.α A) ∘ F.F₁ (F².F₁ f) ∘ F².F₁ (ι.α B) ∘ F.F₁ (δ.α B)
  C5 f =
    Equiv.sym (homomorphism F) ∙
    F.F-resp-≈ C2 ∙
    F.F-resp-≈ (sym-assoc ∙ sym-assoc) ∙
    homomorphism₄ F

  𝐏-unit-lemma : ∀ {A : Obj} → δ.α A ≈ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ∘ ι.α (F.F₀ A)
  𝐏-unit-lemma =
   begin
   _ ≈˘⟨ identityʳ ⟩
   _ ≈⟨ (refl⟩∘⟨ C3) ⟩
   _ ≈˘⟨ assoc ○ assoc ○ assoc ⟩
   _ ≈⟨ ((assoc ○ assoc ○ Equiv.sym C4 ) ⟩∘⟨refl) ⟩
   _ ≈⟨ assoc ⟩
   _ ∎ -- TODO: refactor

  C6 : ∀ {X : Obj} →
   F.F₁ (ι.α X) ∘ δ.α X ≈ id
  C6 {X} = (refl⟩∘⟨ 𝐏-unit-lemma) ○ Equiv.sym C3

  C7 : ∀ {X : Obj} →
   F.F₁ (δ.α X) ∘ ̂η (F.F₀ X) ≈ δ.α X
  C7 {X} = begin
   _ ≈⟨ MR.pullˡ 𝓒 C4 ⟩
   _ ≈⟨ assoc ○ refl⟩∘⟨ assoc ○ (refl⟩∘⟨ (refl⟩∘⟨ assoc)) ⟩ -- TODO: refactor ugly assoc.
   _ ≈⟨  MR.elimʳ 𝓒 (Equiv.sym C3) ⟩
   _ ∎

  C8 : ∀ {X : Obj} →
   F.F₁ (δ.α X) ≈ F.F₁ (̂η (F.F₀ X)) ∘ F².F₁ (δ.α X)
  C8 {X} = F-resp-≈ F (Equiv.sym C7) ○ homomorphism F

  𝐏Functor : Endofunctor 𝓒
  𝐏Functor = record
   { F₀ = λ X → F₀ F X
   ; F₁ = λ f → 𝐏 f
   ; identity = λ { {A} → MR.elim-center 𝓒 (identity F²) ○ C6 }
   ; homomorphism = λ { {X} {Y} {Z} {f} {g} → Equiv.sym (
     assoc ∙ (refl⟩∘⟨ assoc) ∙ 
     (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym C2) ∙ 
     MR.pull-center 𝓒 (Equiv.sym (homomorphism F²))
     )}
   ; F-resp-≈ = λ f≈g → refl⟩∘⟨ (F-resp-≈ F² f≈g ⟩∘⟨refl)
   } where open Functor


module _ {R : Contramonad} where

 open Contramonad R

 F²Monad : Monad 𝓒
 F²Monad = record
   { F = F²
   ; η = ntHelper (record
     { η = λ X → ̂η X
     ; commute = λ _ → C1
     })
   ; μ = ntHelper (record
     { η = λ X → F₁ F (δ.α (F₀ F X) ∘ ι.α (F₀ F X))
     ; commute = λ f → begin
       _ ≈˘⟨ homomorphism F ⟩
       _ ≈⟨ F-resp-≈ F (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym (antiCommute⁻⁺ ι {f = F.F₁ f}))) ⟩
       _ ≈⟨ F-resp-≈ F (sym-assoc ○ sym-assoc ○ sym-assoc) ⟩
       _ ≈⟨ F-resp-≈ F (assoc ○ assoc ⟩∘⟨refl) ⟩
       _ ≈⟨ F-resp-≈ F sym-assoc ⟩
       _ ≈⟨ F-resp-≈ F ((antiCommute⁺⁻ δ {f = F.F₁ f} ⟩∘⟨refl) ⟩∘⟨refl) ⟩
       _ ≈⟨ homomorphism F ⟩
       _ ∎
     })
   ; assoc = λ { {X} → 
   begin _ ≈˘⟨ homomorphism F ⟩
         _ ≈˘⟨ F-resp-≈ F C1 ⟩
         _ ≈⟨ homomorphism F ⟩
         _ ∎ }
   ; sym-assoc = 
      begin 
         _ ≈⟨ {! homomorphism F  !} ⟩
         _ ≈⟨ {!   !} ⟩
         _ ≈⟨ {!   !} ⟩
         _ ∎
   ; identityˡ = λ { {X} →
     Equiv.sym (homomorphism F) ∙
     F-resp-≈ F (homomorphism F ⟩∘⟨refl) ∙
     F-resp-≈ F assoc ∙
     F-resp-≈ F (Equiv.sym C3) ∙
     identity F }
   ; identityʳ = λ {X} →
     (homomorphism F ⟩∘⟨refl) ∙
     assoc ∙
     Equiv.sym C3
   } where open Functor

 𝐏Monad : Monad 𝓒
 𝐏Monad = record
   { F = 𝐏Functor
   ; η = ntHelper (record
     { η = λ X → ι.α X
     ; commute = λ { {X} {Y} f →
       Equiv.sym (MR.pullʳ 𝓒 (assoc ∙ Equiv.sym C1) ∙
       MR.assoc²δγ 𝓒 ∙
       MR.elimˡ 𝓒 C6)}
     })
   ; μ = ntHelper (record
     { η = λ X → ̂μ {X}
     ; commute = λ { {X} {Y} f → {!   !}}
     -- one of the most difficult proofs...
     })
   ; assoc = λ { {X} → {!   !} }
   ; sym-assoc = λ { {X} →  {!   !} }
   ; identityˡ = λ { {X} → 
     assoc ∙ 
     (refl⟩∘⟨ assoc) ∙ 
     (skip-2 (Equiv.sym C2)) ∙ 
     (refl⟩∘⟨ sym-assoc) ∙ 
     (MR.elim-center 𝓒 (Equiv.sym (homomorphism F) ∙ [ F ]-elim C6)) ∙ 
     C6
     }
   ; identityʳ = λ { {X} → MR.assoc²βε 𝓒 ∙ Equiv.sym C3}
   } where open Functor

 ζ : monadMap 𝐏Monad F²Monad
 ζ = record
   { α = ntHelper (record
     { η = δ.α
     ; commute = λ { {X} {Y} f → Equiv.sym C2 }
     })
   ; resp-id = Equiv.refl
   ; resp-mu = λ { {X} → Equiv.sym C4 ∙ (C8 ⟩∘⟨refl) ∙ assoc}
   }