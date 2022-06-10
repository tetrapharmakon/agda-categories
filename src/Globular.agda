{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Data.Product

module Globular {o ℓ e} (ℂ : Category o ℓ e) where

open Category ℂ
open HomReasoning
open Equiv

open import Level
open import Agda.Builtin.Nat
open import Categories.Adjoint
open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian as c
open import Categories.Category.Cocartesian as cc
open import Categories.Category.Cocomplete.Finitely ℂ
open import Categories.Category.Complete.Finitely ℂ
open import Categories.Diagram.Coequalizer ℂ
open import Categories.Diagram.Equalizer ℂ
open import Categories.Diagram.Pullback ℂ
open import Categories.Functor.Core
open import Categories.Morphism.Reasoning ℂ
open import Categories.Object.Coproduct
open import ArrowNet


{-
CATEGORIES
===
arrow network; an arrow network is a set equipped with an action
of the free monoid on two generators, called s,t to make evident
that an arrow network is also a special kind of graph (where the
object of vertices and of edges coincide).
-}
record GlobObj : Set (o ⊔ ℓ ⊔ e) where
  constructor globj
  field
    E : Nat → Obj
    s t : ∀ (n : Nat) → E (n + 1) ⇒ E n
    --
    gi-s : ∀ {n : Nat} → s n ∘ s (n + 1) ≈ s n ∘ t (n + 1)
    gi-t : ∀ {n : Nat} → t n ∘ s (n + 1) ≈ t n ∘ t (n + 1)


record GlobMor (G H : GlobObj) : Set (o ⊔ ℓ ⊔ e) where
  constructor glmor
  private
    module G = GlobObj G
    module H = GlobObj H
  field
    f : ∀ (n : Nat) → G.E n ⇒ H.E n
    eq : ∀ {n : Nat} → f n ∘ G.s n ≈ H.s n ∘ f (n + 1)

Globs : Category _ _ _
Globs = record
  { Obj = GlobObj
  ; _⇒_ = λ G H → GlobMor G H
  ; _≈_ = λ {(glmor f eq) (glmor g eq') → ∀ {n : Nat} → f n ≈ g n}
  ; id = glmor (λ _ → id) id-comm-sym
  ; _∘_ = comp
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = λ x → sym x
    ; trans = λ p q → trans p q
    }
  ; ∘-resp-≈ = λ p q → ∘-resp-≈ p q
  } where comp : {A B C : GlobObj} → GlobMor B C → GlobMor A B → GlobMor A C
          comp {globj A s t s-gi t-gi} {globj B s' t' s-gi' t-gi'} {globj C s'' t'' s-gi'' t-gi''} (glmor f eq) (glmor g eq') = glmor (λ n → f n ∘ g n)
            (λ {n} → begin (f n ∘ g n) ∘ s n ≈⟨ assoc ⟩
                           f n ∘ g n ∘ s n ≈⟨ refl⟩∘⟨ eq' ⟩
                           f n ∘ s' n ∘ g (n + 1) ≈⟨ sym assoc ⟩
                           (f n ∘ s' n) ∘ g (n + 1) ≈⟨ eq ⟩∘⟨refl ⟩
                           (s'' n ∘ f (n + 1)) ∘ g (n + 1) ≈⟨ assoc ⟩
                           s'' n ∘ f (n + 1) ∘ g (n + 1) ∎)

C : Functor Globs aNets
C = ?