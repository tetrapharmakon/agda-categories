{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.Monoidal.Instance.Sets using (module Coproduct)

-- Generic instance: all Rosen modules instantiated for Sets,
-- serving as a type-checking test and a concrete example.
module Categories.Rosen.Cartesian.Concrete (o : Level) where
