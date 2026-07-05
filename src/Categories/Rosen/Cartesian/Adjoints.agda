{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level

module Categories.Rosen.Cartesian.Adjoints (o : Level) where

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (refl)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ʳ_)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.Adjoint using (_⊣_)

open import Categories.Rosen.Cartesian.Sets
open Sets-MonoidalClosed {o}

private
  S : Category (suc o) o o
  S = Sets o

  M : Monoidal S
  M = Sets-Monoidal

  Cl : Closed M
  Cl = Sets-Closed

open Category S
open HomReasoning

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)

open import Categories.Rosen.Core Cl
open import Categories.Rosen.Tabulator Cl using (𝕋MRS;⟪_,_⟫)
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}

open import Categories.Functor.Profunctor.Tabulator

private
  module CodF = Functor Cod

-- The unique natural transformation Cod ⇒ [A,-] ∘ Cod in Sets (constant).
const-ϕ : (A : Obj) → NaturalTransformation Cod (([ A ,-] ∘F Cod))
const-ϕ A = record
  { η = λ m y a → y
  ; commute = λ { {X} {Y} α {z} → ≡.refl }
  ; sym-commute = λ { {X} {Y} α {z} → ≡.refl }
  }

-- Yoneda: in the Cartesian case, Cod is represented in Arrow S by the terminal arrow ∅ → 1,
-- so Nat(Cod, [A,-]∘Cod) has exactly one element.
yoneda-argument : ∀ A → (ϕ ψ : NaturalTransformation Cod (([ A ,-] ∘F Cod))) → ϕ ≃ ψ
yoneda-argument A ϕ ψ {x} {v} = {!  !}

-- Uniqueness: any such natural transformation equals const-ϕ A.
unique-ϕ : ∀ A → (ϕ : NaturalTransformation Cod (([ A ,-] ∘F Cod))) → const-ϕ A ≃ ϕ
unique-ϕ A ϕ = yoneda-argument A (const-ϕ A) ϕ

-- The left adjoint L : Arrow S → 𝕋MRS.
L : Functor Arr.Arrow 𝕋MRS
L = record
  { F₀ = λ x → 
    let module x = Arr.Morphism x 
    in (x.dom , x.cod) ∣ ⟪ x.arr , const-ϕ (x.dom) ⟫
  ; F₁ = λ { {u} {v} f → 
    let module f = Arr.Morphism⇒ f
        module u = Arr.Morphism u
        module v = Arr.Morphism v
        eq₂-lemma : ∀ {A B} (u : A ⇒ B) → (nHom id ∘ʳ Cod) ∘ᵥ const-ϕ A ≃ (nHom u ∘ʳ Cod) ∘ᵥ const-ϕ B
        eq₂-lemma u = {!!}
    in f.dom⇒ , f.cod⇒ ∥ (f.square , eq₂-lemma f.dom⇒)}
  ; identity = {!  !}
  ; homomorphism = {!  !}
  ; F-resp-≈ = {!  !}
  }
{-
L = record
  { F₀ = λ m → (Arr.Morphism.dom m , Arr.Morphism.cod m) ∣ ⟪ Arr.Morphism.arr m , const-ϕ (Arr.Morphism.dom m) ⟫
  ; F₁ = λ { {m} {n} α →
      let A₁ = Arr.Morphism.dom m
          A₂ = Arr.Morphism.dom n
          u = Arr.Morphism⇒.dom⇒ α
          v = Arr.Morphism⇒.cod⇒ α
          square = Arr.Morphism⇒.square α
          eq₂ : (nHom id ∘ʳ Cod) ∘ᵥ const-ϕ A₁ ≃ (nHom u ∘ʳ Cod) ∘ᵥ const-ϕ A₂
          eq₂ = λ {x} → {!!}
      in u , v ∥ (square , eq₂) }
  ; identity = Equiv.refl , Equiv.refl
  ; homomorphism = Equiv.refl , Equiv.refl
  ; F-resp-≈ = λ { (u≈u′ , v≈v′) → u≈u′ , v≈v′ }
  }

-- The adjunction L ⊣ V₁.
L⊣V₁ : L ⊣ V₁
L⊣V₁ = {!!}
-}