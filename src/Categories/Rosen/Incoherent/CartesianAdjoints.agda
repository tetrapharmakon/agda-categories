{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Adjoint using (_⊣_)
open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.TwistedArrow
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Data.Product using (_,_; Σ)
open import Level using (Level; 0ℓ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)

module Categories.Rosen.Incoherent.CartesianAdjoints (o : Level) where

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
open Closed Cl using ([_,_]₀)
open HomReasoning

open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Elements Cl using (τ′[iMR2]; ⟅_⟆f)
open import Categories.Rosen.Incoherent.Functors Cl using ([_]f)

-- module Arr = Categories.Category.Construction.Arrow S
module Tw = Categories.Category.Construction.TwistedArrow S

-- The Cartesian constant repair map.  Its implementation and uniqueness
-- properties are left for the later adjunction development.
const-Φ : (A : Obj) → ∀ {B} → B ⇒ [ A , B ]₀
const-Φ A a b = a

-- Incoherent counterparts of the left adjoints in Cartesian.Adjoints.
L : Functor Arr.Arrow τ[iMR2]
L = record
  { F₀ = λ { record { dom = A ; cod = B ; arr = u } → record { A = A ; B = B ; ξ = ⟪ u , const-Φ A ⟫ } }
  ; F₁ = λ {(mor⇒ {dom⇒ = l} {cod⇒ = r} square) → record { l = l ; r = r ; eqf = square ; eqΦ = λ {x} → ≡-refl } }
  ; identity = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z
  }


open import Categories.Category.Construction.TwistedArrow S renaming (Morphism to tMorphism; Morphism⇒ to tMorphism⇒; mor⇒ to tmor⇒)

L′ : Functor Tw.TwistedArrow τ′[iMR2]
L′ = record
  { F₀ = λ x → let module x = tMorphism x in record { A = x.dom ; B = x.cod ; ξ = ⟪ x.arr , (λ z z₁ → z) ⟫ }
  ; F₁ = λ f →  let module f = tMorphism⇒ f in record { l = f.dom⇐ ; r = f.cod⇒ ; eqf = f.square ; eqΦ = λ {x} → ≡-refl }
  ; identity = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z
  }


open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

-- THE ADJUNCTIONS DO NOT EXIST, and this file no longer pretends otherwise.
--
-- L and L′ above are complete and unconditional: they equip an arrow with the
-- constant repair map, and every law is refl.  They are the paper's `ell` and
-- `ell_prime`.
--
-- What does not exist is their adjointness to [_]f and ⟅_⟆f.  The counit at an
-- incoherent system ⟨f,Φ⟩ would be a morphism ⟨f,const-Φ⟩ → ⟨f,Φ⟩ over the
-- identities, whose eqΦ field forces Φ = const-Φ -- that is, forces every
-- Φ : B → (A → B) to satisfy Φ b a ≡ b, which is false for an unconstrained Φ
-- (take A = B = Bool and Φ b a = a).
--
-- In the coherent Cartesian setting the same computation goes through, but only
-- because Nat(id,[A,-]) is a singleton over Sets, which needs 1 to be a
-- generator (Cartesian/WellPointed.agda).  That hypothesis is exactly what the
-- paper's cartesian_w_nontrivial_MRs shows one must abandon to have nontrivial
-- coherent systems at all, so the repair buys nothing.
--
-- §3 of the paper says the same, and says it negatively: the displayed diagram
-- there is labelled `not_adjoints`, and a footnote locates the obstruction.
-- Two results asserting the adjunctions, each inhabited by a postulate, used to
-- stand here; they have been removed.
