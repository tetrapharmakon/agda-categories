{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level using (Level; 0ℓ; suc)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Construction.TwistedArrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor)
open import Categories.Adjoint using (_⊣_)
open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence; subst) renaming (refl to ≡-refl; sym to ≡-sym)
open import Data.Product using (_,_; Σ)
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
open import Categories.Rosen.Incoherent.Elements Cl using (τ'[iMR2]; 𝕃)
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

L' : Functor Tw.TwistedArrow τ'[iMR2]
L' = record
  { F₀ = λ x → let module x = tMorphism x in record { A = x.dom ; B = x.cod ; ξ = ⟪ x.arr , (λ z z₁ → z) ⟫ }
  ; F₁ = λ f →  let module f = tMorphism⇒ f in record { l = f.dom⇐ ; r = f.cod⇒ ; eqf = f.square ; eqΦ = λ {x} → ≡-refl }
  ; identity = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z
  }


open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

L⊣A : L ⊣ [_]f
L⊣A = record 
  { unit = ntHelper (record { η = λ X → mor⇒ {dom⇒ = id} {cod⇒ = id} ≡-refl ; commute = λ {X} {Y} f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) }) 
  ; counit = ntHelper (record 
    { η = λ X → record { l = id ; r = id ; eqf = λ {x} → ≡-refl 
      ; eqΦ = {!  !} } 
    ; commute = λ f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) }) 
  ; zig = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) 
  ; zag = λ {B} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) 
  }

L'⊣𝕃 : L' ⊣ 𝕃
L'⊣𝕃 = record 
  { unit = ntHelper (record { η = λ X → tmor⇒ λ {x} → ≡-refl ; commute = λ f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) }) 
  ; counit = ntHelper (record { η = λ X → record { l = id ; r = id ; eqf = λ {x} → ≡-refl ; eqΦ = {!  !} } ; commute = λ {X} {Y} f → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) }) 
  ; zig = λ {A} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) 
  ; zag = λ {B} → (λ {x} → ≡-refl) , (λ {x} → ≡-refl) 
  }
