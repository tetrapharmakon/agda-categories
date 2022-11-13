module Categories.ParametricAdjoint where


open import Level


open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Adjoint
open import Categories.Category.Construction.Functors

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e


record ParametricAdjoint (L : Functor C (Functors D E)) (R : Functor (Category.op C) (Functors E D)) : Set _ where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module L = Functor L
    module R = Functor R
  field
    areAdjoint : {A : Category.Obj C} → Adjoint (L.F₀ A) (R.F₀ A)
