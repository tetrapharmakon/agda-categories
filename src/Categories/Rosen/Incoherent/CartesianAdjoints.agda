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
  ; F₁ = λ {(mor⇒ {dom⇒ = l} {cod⇒ = r} square) → record { l = l ; r = r ; eqf = square ; eqΦ = {!   !} } }
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }

L' : Functor Tw.TwistedArrow τ'[iMR2]
L' = {!!}

L⊣A : L ⊣ [_]f
L⊣A = {!!}

L'⊣𝕃 : L' ⊣ 𝕃
L'⊣𝕃 = {!!}
