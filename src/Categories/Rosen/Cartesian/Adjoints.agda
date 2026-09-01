{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Level

-- Instances of the Rosen constructions for the Cartesian (Sets) case.
-- In this setting, V₁ and U₁ acquire left adjoints (L and Lʹ).
-- Over Sets the repair data is rigid: Nat(id, [A,-]) is a singleton, because 1
-- is a generator of Sets, so the unique repair map is const-Φ and is available
-- wherever needed: an arrow is sent to the (M,R)-system / element of ElMRS
-- with that constant repair map.  See `Nat-id-hom-unique` below, whose name is
-- now historical --- the argument is well-pointedness, not Yoneda.
-- Exports: const-Φ, Nat-id-hom-unique, unique-Φ, L, L⊣V₁, L′, L′⊣U₁.
module Categories.Rosen.Cartesian.Adjoints (o : Level) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Category using (Category)
open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Sets
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
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

-- Arrow(C); see the note in Coherent/ProElements.agda.
module Arr = Categories.Category.Construction.Arrow S

open import Categories.Rosen.Coherent.IdCore Cl
open import Categories.Rosen.Coherent.ProElements Cl {F = MRS-Profunctor} using (ElMRS;Elts₀;Elts⇒;U₁)
open import Categories.Rosen.Coherent.Tabulator Cl using (𝕋MRS; V₁)

open import Categories.Functor.Profunctor.Tabulator

-- const-Φ A: the unique natural transformation id ⇒ [A,-] in Sets.
-- At an object X it "repairs" an element by returning the very element given:
-- the map X → (A → X) that is constant in A (`a ↦ y`).
const-Φ : (A : Obj) → NaturalTransformation idF ([ A ,-])
const-Φ A = record
  { η = λ X y a → y
  ; commute = λ { _ → ≡.refl }
  ; sym-commute = λ { _ → ≡.refl }
  }

-- Yoneda: in the Cartesian case, Cod is represented in Arrow S by the terminal arrow ∅ → 1,
-- so Nat(Cod, [A,-]∘Cod) has exactly one element.
-- Nat-id-hom-unique: in Sets, Cod is represented by the terminal arrow,
-- so Nat(Cod, [A,-]∘Cod) is a singleton.
-- The singleton property of Nat(id, [A,-]) in Sets, on which every adjunction
-- in this file rests, is proved in Categories.Rosen.Cartesian.WellPointed: it
-- is the statement that 1 generates Sets, and it belongs there rather than
-- here because it says nothing about (M,R)-systems.  Read that module's header
-- for why the hypothesis is worth naming: in the topos of C₂-sets it fails,
-- which is exactly what cartesian_w_nontrivial_MRs exploits.
open import Categories.Rosen.Cartesian.WellPointed o using (Nat-id-hom-unique)

-- Uniqueness: any such natural transformation equals const-Φ A.
-- unique-Φ: every such Φ equals const-Φ A.
unique-Φ : ∀ A → (Φ : NaturalTransformation idF ([ A ,-])) → const-Φ A ≃ Φ
unique-Φ A Φ = Nat-id-hom-unique A (const-Φ A) Φ

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
      ; eq = lift ( square
                  , (λ {x} {z} →
                      Nat-id-hom-unique A
                        (nHom (id {A}) ∘ᵥ const-Φ A)
                        (nHom u ∘ᵥ const-Φ B)
                        {x} {z}) )
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
    in record { l = u ; r = v ; eqElts = lift (square , (λ {x} {x = x₁} → refl)) } }
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
            lift ( refl
                 , (λ {x} {z} →
                     Nat-id-hom-unique A
                       (nHom (id {A}) ∘ᵥ const-Φ A)
                       (nHom (id {A}) ∘ᵥ Φ)
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
      ; eqElts = lift (refl ,
          let module X = Elts₀ X in
          Nat-id-hom-unique X.A (nHom (id {X.A}) ∘ᵥ const-Φ X.A) (MR2.Φ X.el))
      }
    ; commute = λ _ → refl
              , (λ {x} → refl)
    })
  ; zig = refl , refl
  ; zag = refl , refl
  }
