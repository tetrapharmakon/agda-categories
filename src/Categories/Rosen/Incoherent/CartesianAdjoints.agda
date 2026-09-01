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

-- ┌──────────────────────────────────────────────────────────────────────────┐
-- │ KNOWN-FALSE POSTULATE.  Everything named UNSOUND-* in Categories.Rosen is │
-- │ a statement this development knows to be FALSE.  It is postulated only so │
-- │ that the shape of the obstruction is visible and typed; nothing that      │
-- │ depends on it is verified.  `grep -rn UNSOUND src/Categories/Rosen/`      │
-- │ enumerates the whole debt.                                               │
-- └──────────────────────────────────────────────────────────────────────────┘
--
-- The counits below cannot be constructed for arbitrary incoherent systems.
-- Since L and L′ equip an arrow with the constant repair map, their eqΦ fields
-- would require every Φ : B → (A → B) to be that constant map.  That is false
-- for an unconstrained Φ (take A = B = Bool and Φ b a = a), so the statement
-- below is an obstruction, not missing equational reasoning.
--
-- In the coherent Cartesian construction, Φ is natural in the arrow variable
-- and a Yoneda argument proves that it is the unique constant repair map
-- (Cartesian/Adjoints.agda, `yoneda-argument`/`unique-Φ`, both proved).  An
-- iMR2 stores no such naturality data, so that argument is unavailable here.
--
-- NOTE ON THE PAPER.  §3 of "The Rosen fibration" states the matching claim
-- correctly and negatively: the displayed diagram there is labelled
-- `not_adjoints`, and the prose reads "one can check that L and L′ fall just
-- short of satisfying the adjunction property".  The two results below assert
-- the opposite of what the paper asserts, and are retained only to record the
-- shape of the failed construction.  THEY MUST NOT BE CITED AS RESULTS.
postulate
  UNSOUND-Φ-is-constant :
    ∀ {A B : Obj} (Φ : B ⇒ [ A , B ]₀) {b : B} → Φ b ≡ (λ _ → b)

L⊣A : L ⊣ [_]f
L⊣A = record
  { unit = ntHelper (record { η = λ X → mor⇒ {dom⇒ = id} {cod⇒ = id} ≡-refl ; commute = λ {X} {Y} f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) })
  ; counit = ntHelper (record
    { η = λ X → record { l = id ; r = id ; eqf = λ {x} → ≡-refl
      ; eqΦ = λ {x} → UNSOUND-Φ-is-constant (iMR2.Φ (iMR2₀.ξ X)) }
    ; commute = λ f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) })
  ; zig = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; zag = λ {B} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  }

L′⊣⟅⟆f : L′ ⊣ ⟅_⟆f
L′⊣⟅⟆f = record
  { unit = ntHelper (record { η = λ X → tmor⇒ λ {x} → ≡-refl ; commute = λ f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) })
  ; counit = ntHelper (record { η = λ X → record { l = id ; r = id ; eqf = λ {x} → ≡-refl ; eqΦ = UNSOUND-Φ-is-constant (iMR2.Φ (iMR2₀.ξ X)) } ; commute = λ {X} {Y} f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) })
  ; zig = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; zag = λ {B} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  }
