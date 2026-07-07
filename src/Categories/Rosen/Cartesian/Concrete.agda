{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level

-- Generic instance: all Rosen modules instantiated for Sets,
-- serving as a type-checking test and a concrete example.
module Categories.Rosen.Cartesian.Concrete (o : Level) where
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Cocartesian using (BinaryCoproducts)

open import Categories.Rosen.Cartesian.Sets
open Sets-MonoidalClosed {o}

private
  S : Category (suc o) o o
  S = Sets o

  M : Monoidal S
  M = Sets-Monoidal

  Cl : Closed M
  Cl = Sets-Closed

open import Categories.Rosen.Core Cl
open import Categories.Rosen.Tabulator Cl
open import Categories.Rosen.TotalCategory Cl
open import Categories.Rosen.TabEquivalence Cl
open import Categories.Rosen.FibreA Cl
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor}
-- HigherMRS has holes in MRS-chain; skip until filled.
open import Categories.Rosen.HigherMRS Cl
open import Categories.Rosen.Adjunction.TotRep Cl
open import Categories.Rosen.Incoherent.Core Cl
open import Categories.Rosen.Incoherent.Fibred Cl

open import Categories.Category.Monoidal.Instance.Sets using (module Coproduct)

private
  BC : BinaryCoproducts S
  BC = Coproduct.Sets-has-all

-- Algebras has unresolved level errors when instantiated for Sets.
-- open import Categories.Rosen.Algebras M Cl BC
