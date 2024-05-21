
{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Core 
open import Categories.Functor
open import Categories.Monad
open import Categories.Category.Product
open import Categories.Category.Construction.Functors

module FOEM {o ℓ e o' ℓ' e'} {params : Category o ℓ e} {carriers : Category o' ℓ' e'} {F : Functor params (Monads carriers)} where

open import Level
module F = Functor F

open import Data.Product using (_,_; _×_)
open import Categories.Adjoint
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.NaturalTransformation as NT -- using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism.Functors


open import Categories.Category.Construction.EilenbergMoore as EM
open import Categories.Adjoint.Construction.EilenbergMoore as EMF

open Module
open Module⇒
open NaturalTransformation
open Monad⇒

import Categories.Morphism.Reasoning carriers as MR
open import BetterReasoning carriers

record FOEM-objects : Set (o ⊔ o' ⊔ ℓ' ⊔ e') where
  constructor ⟦_,_⟧
  field
    𝕌 : Category.Obj params
    emalg : Module (F.F₀ 𝕌)

open FOEM-objects
module P = Category params 
module C = Category carriers

reindex : {A' : P.Obj} (E : FOEM-objects) (u : A' P.⇒ 𝕌 E) → Module (F.F₀ A')
reindex {A'} E u = 
    let EE = A (emalg E) in 
    let ξ = action (emalg E) in 
    let TuX = η (α (F.F₁ u)) (A (emalg E)) in record 
      { A = EE 
      ; action = ξ C.∘ TuX
      ; commute = let open C.HomReasoning in 
        begin _ ≈⟨ ((refl⟩∘⟨ homomorphism ((Monad.F (F.F₀ A'))))) ⟩ 
              {!   !} ≈⟨ C.sym-assoc ⟩
              {!   !} ≈⟨ (MR.pullʳ (commute (α (F.F₁ u)) ξ) ⟩∘⟨refl) ⟩
              {!   !} ≈⟨ {!   !} ⟩
              _ ≈˘⟨ MR.pullʳ (α-mult (F.F₁ u)) ⟩ 
              _ ∎ 
      ; identity = let open C.HomReasoning in 
        begin _ ≈⟨ MR.pullʳ (Equiv.sym (α-unit (F.F₁ u))) ⟩ 
              _ ≈⟨ identity (emalg E) ⟩ 
              _ ∎ 
      } where open Functor

syntax reindex E u = u ̂* E

record FOEM-arrows (E E' : FOEM-objects) : Set (ℓ ⊔ ℓ' ⊔ e ⊔ e') where
    constructor ⟅_,_⟆
    field
        p⇒ : (params Category.⇒ 𝕌 E) (𝕌 E')
        c⇒ : Module⇒ (F.F₀ (𝕌 E)) (emalg E) (p⇒ ̂* E')

open FOEM-arrows

FOEM∘ : {X Y Z : FOEM-objects} →
      FOEM-arrows Y Z → FOEM-arrows X Y → FOEM-arrows X Z
FOEM∘ {X} {Y} {Z} = λ { ⟅ p⇒ , c⇒ ⟆ ⟅ p⇒' , c⇒' ⟆ → 
  ⟅ p⇒ P.∘ p⇒' 
  , record 
    { arr = arr c⇒ C.∘ arr c⇒' 
    ; commute = 
      let open C.HomReasoning in  
      let z = action (emalg Z) in
      let α = η (α (F.F₁ p⇒)) (A (emalg Z)) in 
      let α' = η (Monad⇒.α (F.F₁ p⇒')) (A (emalg Y)) in
      begin _ ≈⟨ MR.pullʳ (Module⇒.commute c⇒') ⟩ 
            _ ≈⟨ MR.pullˡ (MR.pullˡ (Module⇒.commute c⇒)) ⟩ 
            _ ≈⟨ ((C.assoc ⟩∘⟨refl) ⟩∘⟨refl) ⟩ 
            {!  !} ≈⟨ {!   !} ⟩ 
            {!  !} ≈⟨ {!   !} ⟩ 
            _ ≈˘⟨ (refl⟩∘⟨ Functor.homomorphism (Monad.F (F.F₀ (𝕌 X)))) ⟩ 
            _ ∎} 
  ⟆} where open C


FOEM : Category (o ⊔ o' ⊔ ℓ' ⊔ e') (ℓ ⊔ e ⊔ ℓ' ⊔ e') (e ⊔ e')
FOEM = record
  { Obj = FOEM-objects
  ; _⇒_ = FOEM-arrows
  ; _≈_ = λ x y → let f = Module⇒.arr (c⇒ x) in 
                  let g = Module⇒.arr (c⇒ y) in 
                  let u = p⇒ x in 
                  let v = p⇒ y in 
                    (u P.≈ v) × (f C.≈ g)
  ; id = λ { {A} → let FF = Monad.F (F.F₀ (𝕌 A)) in record 
    { p⇒ = P.id 
    ; c⇒ = record 
      { arr = C.id 
      ; commute = let open C.HomReasoning in 
        begin _ ≈⟨ identityˡ ⟩ 
              _ ≈˘⟨ MR.elimʳ F.identity ⟩ 
              _ ≈˘⟨ MR.elimʳ (Functor.identity FF) ⟩ 
              _ ∎
      } 
    }}
  ; _∘_ = FOEM∘
  ; assoc = P.assoc , C.assoc
  ; sym-assoc = P.sym-assoc , C.sym-assoc
  ; identityˡ = P.identityˡ , C.identityˡ
  ; identityʳ = P.identityʳ , C.identityʳ
  ; identity² = P.identity² , C.identity²
  ; equiv = record 
    { refl = P.Equiv.refl , C.Equiv.refl 
    ; sym = λ {(fst , snd) → P.Equiv.sym fst , C.Equiv.sym snd }
    ; trans = λ {(fst , snd) (fst₁ , snd₁) → 
      P.Equiv.trans fst fst₁ , C.Equiv.trans snd snd₁}
    }
  ; ∘-resp-≈ = λ {(dis , dat) (dis' , dat') → P.∘-resp-≈ dis dis' , C.∘-resp-≈ dat dat'}
  }

Π : Functor FOEM params 
Π = record
  { F₀ = λ {⟦ 𝕌 , _ ⟧ → 𝕌}
  ; F₁ = λ {record { p⇒ = p⇒ ; c⇒ = c⇒ } → p⇒}
  ; identity = P.Equiv.refl
  ; homomorphism = P.Equiv.refl
  ; F-resp-≈ = λ { {X} {Y} {f} {g} (fst , _) → fst}
  }

V : Functor FOEM carriers
V = record
  { F₀ = λ {⟦ 𝕌 , alg ⟧ → A alg}
  ; F₁ = (λ { record { p⇒ = _ ; c⇒ = c⇒ } → arr c⇒ })
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ { {X} {Y} {f} {g} (_ , snd) → snd }
  }

⟨Π,V⟩ : Functor FOEM (Product params carriers)
⟨Π,V⟩ = Π ※ V

-- [...]

open import Categories.Object.Initial

open Initial

Φ : (ph⊥ : Initial params) → Functor carriers FOEM
Φ ph⊥ = let Fᵀ = Free (F.F₀ (⊥ ph⊥)) in record
  { F₀ = λ X → ⟦ ⊥ ph⊥ , F₀ Fᵀ X ⟧
  ; F₁ = λ { {A} {B} f → ⟅ P.id , record 
    { arr = arr (F₁ Fᵀ f) 
    ; commute = let open C.HomReasoning in
      begin _ ≈⟨ commute (F₁ Fᵀ f) ⟩ 
            _ ≈˘⟨ (MR.elimʳ F.identity ⟩∘⟨refl) ⟩ 
            _ ∎
    } ⟆}
  ; identity = P.Equiv.refl , identity Fᵀ
  ; homomorphism = P.Equiv.sym P.identity² , homomorphism Fᵀ
  ; F-resp-≈ = λ { {A} {B} {f} {g} x → P.Equiv.refl , F-resp-≈ Fᵀ x }
  } where open Functor


Φ⊣V : (ph⊥ : Initial params) → Φ ph⊥ ⊣ V 
Φ⊣V ph⊥ = record 
  { unit = ntHelper (record 
    { η = λ X → Monad.η.η (F.F₀ (⊥ ph⊥)) X
    ; commute = λ f → commute (Monad.η (F.F₀ (⊥ ph⊥))) f 
    }) 
  ; counit = ntHelper (record 
    { η = λ {⟦ 𝕌 , ξ ⟧ → ⟅ ! ph⊥ , record 
      { arr = action ξ C.∘ η (α (F.F₁ (! ph⊥))) (A ξ)
      ; commute = {!   !} } ⟆}
    ; commute = λ { {X} {Y} ⟅ u , φ ⟆ →  {!   !} , {!   !} }
    }) 
  ; zig = {!   !} 
  ; zag = {!   !} 
  } where open Functor