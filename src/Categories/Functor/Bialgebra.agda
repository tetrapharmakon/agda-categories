{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Bialgebra where

open import Level
open import Categories.Category using (Category)
open import Categories.Functor
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)

{-
given two endofunctors T and F on a category C, we can define a
(T,F)-bialgebra to be an object of C equipped with the structure of a
T-algebra and an F-coalgebra, i.e. just a triple (A,a,c), where a:TA→A
and c:A→FA.  μ is a distributive law (of T over F): a natural
transformation μ:TF→FT.  A μ-bialgebra is a (T,F)-bialgebra (A,a,c)
such that c∘a=Fa∘μ_A∘Tc [category theory - How are F-bialgebras
defined? - Mathematics Stack Exchange]
(https://math.stackexchange.com/questions/3057781/how-are-f-bialgebras-defined#answer-3057859)

See also: header comment in `Categories.Category.Construction.mu-Bialgebras`
-}

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} where

  record μ-Bialgebra (T F : Endofunctor C) (μ : DistributiveLaw T F)
       : Set (o ⊔ ℓ ⊔ e) where
    open Category C
    open Functor
    open NaturalTransformation
    field
      A : Obj
      a₁ : F-Algebra-on T A
      c₁ : F-Coalgebra-on F A
    module F = Functor F
    module T = Functor T
    field
      respects-μ : c₁ ∘ a₁ ≈ ((F.₁) a₁) ∘ (μ .η A) ∘ ((T.₁) c₁)
    --to access the (co)algebras induced by the morphisms:
    alg : F-Algebra T
    alg = to-Algebra a₁

    coalg : F-Coalgebra F
    coalg = to-Coalgebra c₁

  record μ-Bialgebra-Morphism {T F : Endofunctor C} {μ : DistributiveLaw T F} (X Y : μ-Bialgebra T F μ) : Set (o ⊔ ℓ ⊔ e) where
    open Category C using (_⇒_)
    private
      module X = μ-Bialgebra X
      module Y = μ-Bialgebra Y
    field
      f : X.A ⇒ Y.A
      f-is-alg-morph : is-F-Algebra-Morphism X.alg Y.alg f
      f-is-coalg-morph : is-F-Coalgebra-Morphism X.coalg Y.coalg f

    alg-morph : F-Algebra-Morphism X.alg Y.alg
    alg-morph = record { f = f; commutes = f-is-alg-morph }

    coalg-morph : F-Coalgebra-Morphism X.coalg Y.coalg
    coalg-morph = record { f = f; commutes = f-is-coalg-morph }
