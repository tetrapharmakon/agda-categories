{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level

-- Instances of the Rosen constructions for the Cartesian (Sets) case.
-- In this setting, V₁ and U₁ acquire left adjoints (L and Lʹ).
-- Over Sets the repair data is rigid: Nat(Cod, [A,-]∘Cod) is a singleton,
-- so the unique repair map is const-Φ and is available wherever needed: an
-- arrow is sent to the (M,R)-system / element of ElMRS with that constant
-- repair map.
-- Exports: const-Φ, yoneda-argument, unique-Φ, L, L⊣V₁, L′, L′⊣U₁.
module Categories.Rosen.Cartesian.Adjoints (o : Level) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ʳ_;ntHelper)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Reasoning.Setoid as SetoidR

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
open HomReasoning

open Closed Cl using ([-,-]; [_,_]₀; [_,-]; [-,_]; [_,_]₁)

open import Categories.Rosen.Coherent.Core Cl
open import Categories.Rosen.Coherent.ProElements Cl {F = MRS-Profunctor} using (ElMRS;Elts₀;Elts⇒;U₁)
open import Categories.Rosen.Coherent.Tabulator Cl using (𝕋MRS; V₁)

open import Categories.Functor.Profunctor.Tabulator

private
  module CodF = Functor Cod

-- The unique natural transformation Cod ⇒ [A,-] ∘ Cod in Sets (constant).
-- const-Φ A: the unique natural transformation Cod ⇒ [A,-]∘Cod in Sets (constant).
-- Intuitively, for a metabolic arrow X → B this "repairs" B by returning the
-- very element given: the map B → (A → B) that is constant in A (`a ↦ y`).
const-Φ : (A : Obj) → NaturalTransformation Cod (([ A ,-] ∘F Cod))
const-Φ A = record
  { η = λ m y a → y
  ; commute = λ { _ → ≡.refl }
  ; sym-commute = λ { _ → ≡.refl }
  }

-- Yoneda: in the Cartesian case, Cod is represented in Arrow S by the terminal arrow ∅ → 1,
-- so Nat(Cod, [A,-]∘Cod) has exactly one element.
-- yoneda-argument: in Sets, Cod is represented by the terminal arrow,
-- so Nat(Cod, [A,-]∘Cod) is a singleton.
yoneda-argument : ∀ A → (Φ ψ : NaturalTransformation Cod (([ A ,-] ∘F Cod))) → Φ ≃ ψ
yoneda-argument A Φ ψ {X} {z} =
  let α : Arr.Morphism⇒ ⊤-arr X
      α = record { dom⇒ = λ { (lift ()) } ; cod⇒ = λ _ → z ; square = λ { {lift ()} } }
  in extensionality {f = NaturalTransformation.η Φ X z} {g = NaturalTransformation.η ψ X z} λ a →
    ≡.trans
      (≡.cong (λ f → f a) (NaturalTransformation.commute Φ α {x = lift tt}))
      (≡.sym (≡.cong (λ f → f a) (NaturalTransformation.commute ψ α {x = lift tt})))
  where
    ⊤-arr : Arr.Morphism
    ⊤-arr = record { dom = Lift o ⊥ ; cod = Lift o ⊤ ; arr = λ { (lift ()) } }

-- Uniqueness: any such natural transformation equals const-Φ A.
-- unique-Φ: every such Φ equals const-Φ A.
unique-Φ : ∀ A → (Φ : NaturalTransformation Cod (([ A ,-] ∘F Cod))) → const-Φ A ≃ Φ
unique-Φ A Φ = yoneda-argument A (const-Φ A) Φ

-- The left adjoint L : Arrow S → 𝕋MRS.
-- L: left adjoint to V₁; sends an arrow (A → X) to the trivial (M,R)-system with Φ = const-Φ A.
L : Functor Arr.Arrow 𝕋MRS
L = record
  { F₀ = λ x →
    let module x = Arr.Morphism x
    in (x.dom , x.cod) ∣ ⟪ x.arr , const-Φ (x.dom) ⟫
  ; F₁ = λ { {m} {n} α@(record { dom⇒ = u ; cod⇒ = v ; square = square }) →
    let A = Arr.Morphism.dom m -- m : A ⇒ X
        B = Arr.Morphism.dom n -- n : B ⇒ Y
        -- square : v ∘ m.arr ≈ n.arr ∘ u
        X = Arr.Morphism.cod m
        Y = Arr.Morphism.cod n
        module m = Arr.Morphism m
        module n = Arr.Morphism n
        module p = Functor MRS-Profunctor
        pAY = p.F₀ (A , Y)
        open SetoidR pAY
    in record
      { l = u
      ; r = v
      ; eq = square
           , (λ {x} {z} →
               yoneda-argument A
                 ((nHom (id {A}) ∘ʳ Cod) ∘ᵥ const-Φ A)
                 ((nHom u ∘ʳ Cod) ∘ᵥ const-Φ B)
                 {x} {z})
      } }
  ; identity = λ { {A} → refl , refl }
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} → refl , refl }
  ; F-resp-≈ = λ { {A} {B} {f} {g} (u≈u′ , v≈v′) → u≈u′ , v≈v′ }
  }

open import Categories.Category.Construction.TwistedArrow S renaming (Morphism to tMorphism; Morphism⇒ to tMorphism⇒)

TwSet = TwistedArrow
-- the other functor exists from the twisted arrow category
-- Lʹ: left adjoint to U₁; sends a twisted arrow (A → X) to the corresponding element of ElMRS.
L′ : Functor TwSet ElMRS
L′ = record
  { F₀ = λ x →
    let module x = tMorphism x
    in record { A = x.dom ; B = x.cod ; el = ⟪ x.arr , const-Φ x.dom ⟫ }
  ; F₁ = λ { {m} {n} α@(record { dom⇐ = u ; cod⇒ = v ; square = square }) →
    let A = tMorphism.dom m -- m : A ⇒ X
        B = tMorphism.dom n -- n : B ⇒ Y
        -- square : ...
        X = tMorphism.cod m
        Y = tMorphism.cod n
        module m = tMorphism m
        module n = tMorphism n
        module p = Functor MRS-Profunctor
        pAY = p.F₀ (A , Y)
        open SetoidR pAY
    in record { l = u ; r = v ; eqElts = square , (λ {x} {x = x₁} → refl) } }
  ; identity = λ {A} → (λ {x} → refl) , (λ {x} → refl)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → (λ {x} → refl) , (λ {x} → refl)
  ; F-resp-≈ = λ {A} {B} {f} {g} z → z
  }

-- L⊣V₁: adjunction L ⊣ V₁.
L⊣V₁ : L ⊣ V₁
L⊣V₁ = record
  { unit = ntHelper
    (record
      { η = λ X → mor⇒ {dom⇒ = λ z → z} {cod⇒ = λ z → z} λ {x} → refl
      ; commute = λ f → (λ {x} → refl) , (λ {x} → refl)
      })
  ; counit = ntHelper
    (record
      { η = λ { ((A , B) ∣ ξ) →
          let Φ = MR2.Φ ξ in
          (λ z → z) , (λ z → z) ∥
            ( refl
            , (λ {x} {z} →
                yoneda-argument A
                  ((nHom (id {A}) ∘ʳ Cod) ∘ᵥ const-Φ A)
                  ((nHom (id {A}) ∘ʳ Cod) ∘ᵥ Φ)
                  {x} {z})
            ) }
      ; commute = λ _ → (λ {x} → refl) , (λ {x} → refl)
      })
  ; zig = refl
        , refl
  ; zag = refl
        , refl
  }

-- L′⊣U₁: adjunction L′ ⊣ U₁
L′⊣U₁ : L′ ⊣ U₁
L′⊣U₁ = record
  { unit = ntHelper (record
    { η = λ X → mor⇒ {dom⇐ = id} {cod⇒ = id} λ {x} → refl
    ; commute = λ {X} {Y} f → (λ {x} → refl) , (λ {x} → refl)
    })
  ; counit = ntHelper (record
    { η = λ X → record
      { l = id
      ; r = id
      ; eqElts = refl ,
          let module X = Elts₀ X in
          yoneda-argument X.A ((nHom (id {X.A}) ∘ʳ Cod) ∘ᵥ const-Φ X.A) (MR2.Φ X.el)
      }
    ; commute = λ _ → refl
              , (λ {x} → refl)
    })
  ; zig = refl , refl
  ; zag = refl , refl
  }
