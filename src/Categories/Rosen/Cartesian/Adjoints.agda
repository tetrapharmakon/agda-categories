{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate #-}

open import Level

module Categories.Rosen.Cartesian.Adjoints (o : Level) where

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as ≡
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Categories.Category.Construction.Arrow
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ʳ_;ntHelper)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.Adjoint using (_⊣_)

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

open import Categories.Rosen.Core Cl
open import Categories.Rosen.Tabulator Cl using (𝕋MRS; V₁)
open import Categories.Rosen.ProElements Cl {F = MRS-Profunctor} using (ElMRS;Elts₀;Elts⇒;U₁)

open import Categories.Functor.Profunctor.Tabulator

private
  module CodF = Functor Cod

-- The unique natural transformation Cod ⇒ [A,-] ∘ Cod in Sets (constant).
const-ϕ : (A : Obj) → NaturalTransformation Cod (([ A ,-] ∘F Cod))
const-ϕ A = record
  { η = λ m y a → y
  ; commute = λ { _ → ≡.refl }
  ; sym-commute = λ { _ → ≡.refl }
  }

-- Yoneda: in the Cartesian case, Cod is represented in Arrow S by the terminal arrow ∅ → 1,
-- so Nat(Cod, [A,-]∘Cod) has exactly one element.
yoneda-argument : ∀ A → (ϕ ψ : NaturalTransformation Cod (([ A ,-] ∘F Cod))) → ϕ ≃ ψ
yoneda-argument A ϕ ψ {X} {z} =
  let α : Arr.Morphism⇒ ⊤-arr X
      α = record { dom⇒ = λ { (lift ()) } ; cod⇒ = λ _ → z ; square = λ { {lift ()} } }
  in extensionality {f = NaturalTransformation.η ϕ X z} {g = NaturalTransformation.η ψ X z} λ a →
    ≡.trans
      (≡.cong (λ f → f a) (NaturalTransformation.commute ϕ α {x = lift tt}))
      (≡.sym (≡.cong (λ f → f a) (NaturalTransformation.commute ψ α {x = lift tt})))
  where
    ⊤-arr : Arr.Morphism
    ⊤-arr = record { dom = Lift o ⊥ ; cod = Lift o ⊤ ; arr = λ { (lift ()) } }

-- Uniqueness: any such natural transformation equals const-ϕ A.
unique-ϕ : ∀ A → (ϕ : NaturalTransformation Cod (([ A ,-] ∘F Cod))) → const-ϕ A ≃ ϕ
unique-ϕ A ϕ = yoneda-argument A (const-ϕ A) ϕ

-- The left adjoint L : Arrow S → 𝕋MRS.
L : Functor Arr.Arrow 𝕋MRS
L = record
  { F₀ = λ x → 
    let module x = Arr.Morphism x 
    in (x.dom , x.cod) ∣ ⟪ x.arr , const-ϕ (x.dom) ⟫
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
                 ((nHom (id {A}) ∘ʳ Cod) ∘ᵥ const-ϕ A)
                 ((nHom u ∘ʳ Cod) ∘ᵥ const-ϕ B)
                 {x} {z})
      } }
  ; identity = λ { {A} → refl , refl }
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} → refl , refl }
  ; F-resp-≈ = λ { {A} {B} {f} {g} (u≈u′ , v≈v′) → u≈u′ , v≈v′ }
  }

open import Categories.Category.Construction.TwistedArrow S renaming (Morphism to tMorphism; Morphism⇒ to tMorphism⇒)

TwSet = TwistedArrow
-- the other functor exists from the twisted arrow category 
L' : Functor TwSet ElMRS
L' = record
  { F₀ = λ x → 
    let module x = tMorphism x 
    in record { A = x.dom ; B = x.cod ; el = ⟪ x.arr , const-ϕ x.dom ⟫ }
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
          let ϕ = MR2.ϕ ξ in
          (λ z → z) , (λ z → z) ∥
            ( refl
            , (λ {x} {z} →
                yoneda-argument A
                  ((nHom (id {A}) ∘ʳ Cod) ∘ᵥ const-ϕ A)
                  ((nHom (id {A}) ∘ʳ Cod) ∘ᵥ ϕ)
                  {x} {z})
            ) }
      ; commute = λ _ → (λ {x} → refl) , (λ {x} → refl)
      }) 
  ; zig = refl 
        , refl 
  ; zag = refl 
        , refl 
  }

L'⊣U₁ : L' ⊣ U₁
L'⊣U₁ = record 
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
          {!  !}
            --  yoneda-argument X.A
            --    ((nHom (id {X.A}) ∘ʳ Cod) ∘ᵥ const-ϕ X.A)
            --    (MR2.ϕ X.el)
            --    {x} {z})
      } 
    ; commute = λ _ → refl 
              , (λ {x} → refl) 
    }) 
  ; zig = refl , refl
  ; zag = refl , refl
  }
