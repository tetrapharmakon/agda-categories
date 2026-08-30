{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Variants.FullyPoly {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

private
  postulate
    sorry : ∀ {u} {A : Set u} → A

-- Fully polymorphic natural MR systems

open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Arrow
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product;_⁂_;πʳ)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation;ntHelper; _∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)

import Reason
open Reason C
open HomReasoning

open Closed Cl using (adjoint; unitorˡ;unitorʳ-commute-to; unitorʳ-commute-from;unitorʳ; [-,-]; unit; [_,_]₀; [_,-]; [-,_]; [_,_]₁; _⊗₁_)

module Arr = Categories.Category.Construction.Arrow C

-- Domain functor Arrow(C) → C.
Dom : Functor Arr.Arrow C
Dom = record
  { F₀           = Arr.Morphism.dom
  ; F₁           = Arr.Morphism⇒.dom⇒
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → proj₁ eq
  }

-- Codomain functor Arrow(C) → C.
Cod : Functor Arr.Arrow C
Cod = record
  { F₀           = Arr.Morphism.cod
  ; F₁           = Arr.Morphism⇒.cod⇒
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → proj₂ eq
  }

-- nHom sends f : A ⇒ B to the induced natural transformation [-,f] : [B,-] ⇒ [A,-].
nHom : ∀ {A B} → A ⇒ B → NaturalTransformation ([_,-] B) ([_,-] A)
nHom {A} {B} f = record
  { η = λ X → [ f , id ]₁
  ; commute = λ h → Equiv.sym [ [-,-] ]-commute
  ; sym-commute = λ h → [ [-,-] ]-commute
  }

-- nHom-identity: nHom respects identity.
nHom-identity : ∀ {A} → nHom (id {A}) ≃ idN
nHom-identity = [-,-].identity

_ᵒ×_ : ∀ {o ℓ e} (𝓐 𝓑 : Category o ℓ e) → Category o ℓ e
𝓐 ᵒ× 𝓑 = Product (Category.op 𝓐) 𝓑

C⇒ᵒ×C⇒ = Arr.Arrow ᵒ× Arr.Arrow

-- definition of an (M,R)-system according to Rosen
record MR2 (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  eta-equality
  constructor ⟪_,_⟫
  field
    f : A ⇒ B
    Φ : NaturalTransformation (Cod ∘F πʳ) ([-,-] ∘F (Functor.op Dom ⁂ Cod))

  Φη = NaturalTransformation.η Φ
  Φη₀ = Φη (record { arr = f } , record { arr = f })
  Φcommute = λ {X Y : Category.Obj C⇒ᵒ×C⇒} t → NaturalTransformation.commute Φ {X} {Y} t

-- MR2 as a Setoid: two MR2 elements are equal when their f components are equal
-- and their Φ components are ≃-equal.
MR2-Setoid : Obj → Obj → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
MR2-Setoid A B = record
  { Carrier = MR2 A B
  ; _≈_ = λ (⟪ f , Φ ⟫) (⟪ g , Φ′ ⟫) → (f ≈ g) × (Φ ≃ Φ′)
  ; isEquivalence = record
    { refl = Equiv.refl , (λ {x₁} → Equiv.refl)
    ; sym = λ (pf , k) → Equiv.sym pf , Equiv.sym k
    ; trans = λ (pf₁ , h) (pf₂ , k) → Equiv.trans pf₁ pf₂ , Equiv.trans h k
    }
  }

{-
  X -- u --> Y
  |          |
u |  u ⇒ id  |
  V          |
  Y -------- Y
-}
u⇒1 : ∀ {X Y} (u : X ⇒ Y) → Morphism⇒ C (record {arr = u}) (record {arr = id {Y}})
u⇒1 u = mor⇒ {dom⇒ = u} {cod⇒ = id} refl

{-
X -------- X
|          |
|  id ⇒ u  | u
|          V
X ---u---> Y
-}
1⇒u : ∀ {X Y} (u : X ⇒ Y) → Morphism⇒ C (record { arr = id {X} }) (record {arr = u})
1⇒u u = mor⇒ {dom⇒ = id} {cod⇒ = u} refl

{-
X ---u---> Y
|          |
|  id ⇒ id |
|          |
X ---u---> Y
-}
1⇒1 : ∀ {X Y} (u : X ⇒ Y) → Morphism⇒ C (record { arr = id {X} }) (record { arr = id {Y} })
1⇒1 u = mor⇒ {dom⇒ = u} {cod⇒ = u} (trans identityʳ (sym identityˡ))

open HomReasoning
open MR

module Naturalities {A B X Y} (ξ : MR2 A B) (u : X ⇒ Y) where
  open MR2
  module ξ = MR2 ξ
  u⇒ : Morphism C
  u⇒ = record { arr = u }

  1⇒ : ∀ {X} → Morphism C
  1⇒ {X} = record { arr = id {X} }

  Φid : (X Y : Obj) → Y ⇒ [ X , Y ]₀
  Φid X Y = Φη ξ (1⇒ {X} , 1⇒ {Y})

  ΦYᵤ : Y ⇒ [ Y , Y ]₀
  ΦYᵤ = Φη ξ (1⇒ {Y} , u⇒)

  ΦXᵤ : Y ⇒ [ X , Y ]₀
  ΦXᵤ = Φη ξ (1⇒ {X} , u⇒)

  Φᵤᵤ : Y ⇒ [ X , Y ]₀
  Φᵤᵤ = Φη ξ (u⇒ , u⇒)

  ΦᵤY : Y ⇒ [ X , Y ]₀
  ΦᵤY = Φη ξ (u⇒ , 1⇒ {Y})

  ΦᵤX : X ⇒ [ X , X ]₀
  ΦᵤX = Φη ξ (u⇒ , 1⇒ {X})

  --------------------
  -- naturality on 1⇒u:
  --
  nat-1⇒uᴿ : Φᵤᵤ ∘ u ≈ [ id {X} , u ]₁ ∘ ΦᵤX
  nat-1⇒uᴿ = Φcommute ξ (Category.id Arr.Arrow {A = u⇒} , 1⇒u u)

  nat-1⇒uᴸ : ΦXᵤ ≈ Φᵤᵤ -- ΦXᵤ ∘ id {Y} ≈ [ id {X} , id {Y} ]₁ ∘ Φᵤᵤ
  nat-1⇒uᴸ = sym-id-1 ∙ Φcommute ξ (1⇒u u , Category.id Arr.Arrow {A = u⇒}) ∙ cancel [-,-].identity

  nat-1⇒u² : ΦXᵤ ∘ u ≈ [ id {X} , u ]₁ ∘ ΦᵤX
  nat-1⇒u² = Φcommute ξ (1⇒u u , 1⇒u u)
  -- naturality on u⇒1:
  --
  nat-u⇒1ᴿ : ΦᵤY ≈ Φᵤᵤ -- ΦᵤY ∘ id {Y} ≈ [ id {X} , id {Y} ]₁ ∘ Φᵤᵤ
  -- hence ΦXᵤ ≈ ΦᵤY by transitivity
  nat-u⇒1ᴿ = sym-id-1 ∙ Φcommute ξ (Category.id Arr.Arrow {A = u⇒} , u⇒1 u) ∙ cancel [-,-].identity

  nat-u⇒1ᴸ : Φᵤᵤ ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ -- Φᵤᵤ ∘ id {Y} ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ
  nat-u⇒1ᴸ = sym-id-1 ∙ Φcommute ξ (u⇒1 u , Category.id Arr.Arrow {A = u⇒})

  nat-u⇒1² : ΦᵤY ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ -- ΦᵤY ∘ id {Y} ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ
  nat-u⇒1² = sym-id-1 ∙ Φcommute ξ (u⇒1 u , u⇒1 u)

  -- naturality on 1⇒1:
  --
  nat-1⇒1ᴿ : ΦᵤY ∘ u ≈ [ id {X} , u ]₁ ∘ ΦᵤX
  nat-1⇒1ᴿ = Φcommute ξ (Category.id Arr.Arrow {A = u⇒} , 1⇒1 u)

  nat-1⇒1ᴸ : ΦXᵤ ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ -- ΦXᵤ ∘ id {Y} ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ
  nat-1⇒1ᴸ = sym-id-1 ∙ Φcommute ξ (1⇒1 u , Category.id Arr.Arrow {A = u⇒})

  nat-1⇒1² : Φid X Y ∘ u ≈ [ u , u ]₁ ∘ Φid Y X
  nat-1⇒1² = Φcommute ξ (1⇒1 u , 1⇒1 u)

  -- cross naturalities: both slots change, but by different Arrow morphisms

  nat-1⇒u×u⇒1 : Φid X Y ≈ Φᵤᵤ -- Φid X Y ∘ id {Y} ≈ [ id {X} , id {Y} ]₁ ∘ Φᵤᵤ
  nat-1⇒u×u⇒1 = sym-id-1 ∙ Φcommute ξ (1⇒u u , u⇒1 u) ∙ cancel [-,-].identity

  nat-1⇒u×1⇒1 : Φid X Y ∘ u ≈ [ id {X} , u ]₁ ∘ ΦᵤX
  nat-1⇒u×1⇒1 = Φcommute ξ (1⇒u u , 1⇒1 u)

  nat-u⇒1×1⇒u : Φᵤᵤ ∘ u ≈ [ u , u ]₁ ∘ Φid Y X
  nat-u⇒1×1⇒u = Φcommute ξ (u⇒1 u , 1⇒u u)

  nat-u⇒1×1⇒1 : ΦᵤY ∘ u ≈ [ u , u ]₁ ∘ Φid Y X
  nat-u⇒1×1⇒1 = Φcommute ξ (u⇒1 u , 1⇒1 u)

  nat-1⇒1×1⇒u : ΦXᵤ ∘ u ≈ [ u , u ]₁ ∘ Φid Y X
  nat-1⇒1×1⇒u = Φcommute ξ (1⇒1 u , 1⇒u u)

  nat-1⇒1×u⇒1 : Φid X Y ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ -- Φid X Y ∘ id {Y} ≈ [ u , id {Y} ]₁ ∘ ΦYᵤ
  nat-1⇒1×u⇒1 = sym-id-1 ∙ Φcommute ξ (1⇒1 u , u⇒1 u)

open Naturalities


-- super trivial profunctoriality because Φ does not depend on anything
MRS-Profunctor : Bifunctor (Category.op C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
MRS-Profunctor = record
  { F₀ = λ { (A , B) → MR2-Setoid A B }
  ; F₁ = λ { {(A , B)} {(A′ , B′)} (u , v) → record
    { _⟨$⟩_ = λ {⟪ f , Φ ⟫ → ⟪ v ∘ f ∘ u , Φ ⟫ }
    ; cong = λ { {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} (f≈g , Φ≈Φ′) →
        (∘-resp-≈ Equiv.refl (∘-resp-≈ f≈g Equiv.refl))
      , Φ≈Φ′
      }
    }}
  -- F₁ leaves Φ strictly alone, so every Φ-component below is the hypothesis itself.
  ; identity = λ { {(A , B)} {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} (f≈g , Φ≈Φ′) →
      Equiv.trans identityˡʳ f≈g , Φ≈Φ′ }
  ; homomorphism = λ { {f = (u₁ , v₁)} {g = (u₂ , v₂)} {⟪ f , Φ ⟫} {⟪ g , Φ′ ⟫} (f≈g , Φ≈Φ′) →
      (begin (v₂ ∘ v₁) ∘ f ∘ u₁ ∘ u₂     ≈˘⟨ assoc ○ assoc ⟩
             (((v₂ ∘ v₁) ∘ f) ∘ u₁) ∘ u₂ ≈⟨ (refl⟩∘⟨ f≈g) ⟩∘⟨refl ⟩∘⟨refl ⟩
             (((v₂ ∘ v₁) ∘ g) ∘ u₁) ∘ u₂ ≈⟨ (assoc ⟩∘⟨refl) ○ (assoc ⟩∘⟨refl) ⟩
             (v₂ ∘ (v₁ ∘ (g ∘ u₁))) ∘ u₂ ≈⟨ assoc ○ sym-assoc ○ assoc ⟩
             v₂ ∘ (v₁ ∘ g ∘ u₁) ∘ u₂     ∎)
    , Φ≈Φ′ }
  ; F-resp-≈ = λ x x₁ → (∘-resp-≈ (x .proj₂) (∘-resp-≈ (x₁ .proj₁) (x .proj₁))) , (x₁ .proj₂)
  }
