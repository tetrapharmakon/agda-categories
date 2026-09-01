{-# OPTIONS --safe --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Level using (_⊔_)

module Categories.Rosen.Coherent.TotalCategory {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open Category C

open import Data.Product using (_,_; _×_)

open import Categories.Category.Construction.Arrow
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Profunctor.Tabulator
open import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (_∘ᵥ_) renaming (NaturalTransformation to NT)
open import Categories.Rosen.Coherent.IdCore Cl

open Closed Cl using ([-,-]; [_,-]; [_,_]₁)
open HomReasoning
open MR

-- The total category of the MRS-profunctor tabulator.
-- Its objects are elements of MRS-Profunctor (the tabulator's base, tab₀),
-- i.e. (M,R)-systems; its morphisms make both f and Φ compatible.
-- Equivalent to the tabulator of MRS-Profunctor (see Tabulator.agda).
-- Used by the coreflection in Adjunction/TotRep.agda.

-- A morphism in the total category between two (M,R)-systems x, y: a map
-- l : x.L ⇒ y.L against the domain and r : x.R ⇒ y.R against the codomain,
-- commuting with the process maps (eqf) and the natural repair maps (nat,
-- which yields the pointwise equation eqΦ).
record tot⇒ (x y : tab₀ MRS-Profunctor) : Set (o ⊔ ℓ ⊔ e) where
  constructor [_,_∥_,_]
  module x = tab₀ x
  module y = tab₀ y
  field
    l : x.L ⇒ y.L
    r : x.R ⇒ y.R

  f = MR2.f x.ξ
  g = MR2.f y.ξ

  module Φ = NT (MR2.Φ x.ξ)
  module ψ = NT (MR2.Φ y.ξ)
  module l*ψ = NT (nHom l ∘ᵥ MR2.Φ y.ξ)

  field
    eqf : r ∘ f ≈ g ∘ l
    -- Naturality is now over C, not over Arr(C): one square per morphism of C.
    nat : ∀ {X Y} (h : X ⇒ Y)
        → l*ψ.η Y ∘ h
        ≈ Functor.F₁ [ x.L ,-] h ∘ Φ.η X

  eqΦ : ∀ {X} → l*ψ.η X ≈ Φ.η X
  eqΦ {X} =
    Equiv.sym identityʳ
    ○ nat (id {X})
    ○ elimˡ C [-,-].identity


-- The total category: objects are the tabulator's points (M,R)-systems and
-- morphisms are tot⇒ pairs; equality is componentwise on l and r.
total : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
total = record
  { Obj = tab₀ MRS-Profunctor
  ; _⇒_ = λ s t → tot⇒ s t
  ; _≈_ = λ h k → tot⇒.l h ≈ tot⇒.l k × tot⇒.r h ≈ tot⇒.r k
  ; id = λ { {(A , B) ∣ ⟪ f , Φ ⟫} →
       let module ΦNT = NT Φ
           module l*Φ = NT (nHom id ∘ᵥ Φ)
       in
       [ id , id
       ∥ id-comm-sym C
       , (λ {X} {Y} h →
         elimˡ C [-,-].identity ⟩∘⟨refl
         ○ ΦNT.commute h)
       ]}
  ; _∘_ = λ { {A} {B} {X} t t′ →
       let module t  = tot⇒ t
           module t′ = tot⇒ t′
           module ψ  = NT (MR2.Φ t.y.ξ)
           module Hom[-1] {X} = Functor (appʳ [-,-] X)
           module Hx = Functor [ t′.x.L ,-]
           module Hy = Functor [ t.x.L ,-]
       in
       [ t.l ∘ t′.l , t.r ∘ t′.r ∥
         pullʳ C t′.eqf ○ pullˡ C t.eqf ○ assoc
       , (λ {X} {Y} h →
           begin
             ([ t.l ∘ t′.l , id ]₁ ∘ ψ.η Y) ∘ h             ≈⟨ ∘-resp-≈ (∘-resp-≈ (Hom[-1].homomorphism) Equiv.refl) Equiv.refl ⟩
             (([ t′.l , id ]₁ ∘ [ t.l , id ]₁) ∘ ψ.η Y) ∘ h ≈⟨ ∘-resp-≈ assoc Equiv.refl ○ assoc ⟩
             [ t′.l , id ]₁ ∘ (([ t.l , id ]₁ ∘ ψ.η Y) ∘ h) ≈⟨ (refl⟩∘⟨ t.nat h) ○  sym-assoc ⟩
            ([ t′.l , id ]₁ ∘ Hy.F₁ h) ∘ t.Φ.η X            ≈⟨ (∘-resp-≈ (Equiv.sym [ [-,-] ]-commute) Equiv.refl) ○ assoc ⟩
             Hx.F₁ h ∘ ([ t′.l , id ]₁ ∘ t.Φ.η X)           ≈⟨ refl⟩∘⟨ t′.eqΦ {X = X} ⟩
             Hx.F₁ h ∘ t′.Φ.η X                             ∎)
       ]}
  ; assoc = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv = record
    { refl = Equiv.refl , Equiv.refl
    ; sym = λ { (p , q) → Equiv.sym p , Equiv.sym q }
    ; trans = λ { (p₁ , q₁) (p₂ , q₂) → Equiv.trans p₁ p₂ , Equiv.trans q₁ q₂ }
    }
  ; ∘-resp-≈ = λ { (p₁ , q₁) (p₂ , q₂) → ∘-resp-≈ p₁ p₂ , ∘-resp-≈ q₁ q₂ }
  }
