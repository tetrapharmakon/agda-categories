module PushProdPull where

open import Categories.Category
open import Categories.Category.Cartesian.Bundle
open import Categories.Category.CartesianClosed.Canonical
open import Categories.Category.Core
open import Categories.Category.Product
open import Categories.Diagram.Pullback
open import Categories.Diagram.Pushout
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Data.Product
open import Function using (const)
open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

postulate
 extensionality : ∀ {A B : Set} {f g : A → B} →
  (∀ (x : A) → f x ≡ g x) →
  f ≡ g

data t : Set where
 ⊤ : t

!-unique-lemma : ∀ (x : t) → ⊤ ≡ x
!-unique-lemma ⊤ = refl

arrow : Category (suc zero) zero zero
arrow = record
  { Obj = Σ (Set × Set) (λ x → proj₁ x → proj₂ x)
  ; _⇒_ = arr
  ; _≈_ = _≡_
  ; id = (λ z → z) , λ z → z
  ; _∘_ = λ {A} {B} {C} f g → comp {A} {B} {C} f g
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ {refl refl → refl}
  }
  where
  arr : Rel (Σ (Set × Set) (λ x → proj₁ x → proj₂ x)) zero
  arr ((a , b) , x1) ((c , d) , y1) = (a → c) × (b → d)
  comp : {A B C : Σ (Set × Set) (λ x → proj₁ x → proj₂ x)} → arr B C → arr A B → arr A C
  comp {A} {B} {C} (f0 , f1) (g0 , g1) = (λ x → f0 (g0 x)) , λ x → f1 (g1 x)

open Category arrow

SetC : Category (suc zero) zero zero
SetC =
 record
  { Obj = Set
  ; _⇒_ = λ x y → x → y
  ; _≈_ = _≡_
  ; id = λ x → x
  ; _∘_ = λ f g a → f (g a)
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ {refl refl → refl}
  }

pushout-prod : (f g : Obj) → Obj
pushout-prod ((A0 , A1) , f) ((B0 , B1) , g) = {!   !}
-- Pushout SetC f×1 1×g
--  where
--  f×1 : A0 × B0 → A1 × B0
--  f×1 (a , b) = f a , b
--  1×g : A0 × B0 → A0 × B1
--  1×g (a , b) = a , g b

pullback-hom : (f g : Obj) → Obj
pullback-hom ((A0 , A1) , f) ((B0 , B1) , g) = {!   !}
-- Pullback SetC [f,1] [1,g]
--  where
--  [f,1] : (A1 → B1) → A0 → B1
--  [f,1] u = λ x → u (f x)
--  [1,g] : (A0 → B0) → A0 → B1
--  [1,g] u = λ x → g (u x)

pp-is-functor : Endobifunctor arrow
pp-is-functor =
 record
  { F₀ = F0
  ; F₁ = {!   !}
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }
  where
  F0 : Category.Obj (Categories.Category.Product.Product arrow arrow) → Obj
  F0 x = pullback-hom (proj₁ x) (proj₂ x)
  F1 : {A B : Obj × Obj} → Product arrow arrow Categories.Category.[ A , B ] → arrow Categories.Category.[ F0 A , F0 B ]
  F1 {((A0 , A1) , a) , ((B0 , B1) , b)} {((C0 , C1) , c) , ((D0 , D1) , d)} ((u , v) , s , t) = {!   !}