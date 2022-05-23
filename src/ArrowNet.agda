{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Data.Product

module ArrowNet {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open Equiv

open import Level

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Core
open import Categories.Category.Cocartesian as cc
open import Categories.Object.Coproduct
open import Categories.Adjoint
-- open import Categories.Adjoint.Properties


record ANetObj : Set (o ⊔ ℓ) where
  constructor anetobj
  field
    {X} : Obj
    s t : X ⇒ X

open ANetObj

record GraphObj : Set (o ⊔ ℓ) where
  constructor graphobj
  field
    {E V} : Obj
    s t : E ⇒ V

open GraphObj

record ANetMor (G H : ANetObj) : Set (ℓ ⊔ e) where
  constructor anetmor
  private
    module G = ANetObj G
    module H = ANetObj H
  field
    f : G.X ⇒ H.X
    s-eqv : f ∘ G.s ≈ H.s ∘ f
    t-eqv : f ∘ G.t ≈ H.t ∘ f

open ANetMor

record GraphMor (G H : GraphObj) : Set (ℓ ⊔ e) where
  constructor graphmor
  private
    module G = GraphObj G
    module H = GraphObj H
  field
    fE : G.E ⇒ H.E
    fV : G.V ⇒ H.V
    s-eqv : fV ∘ G.s ≈ H.s ∘ fE
    t-eqv : fV ∘ G.t ≈ H.t ∘ fE

open GraphMor

aNets : Category _ _ _
aNets = record
  { Obj = ANetObj
  ; _⇒_ = λ G H → ANetMor G H
  ; _≈_ = λ u v → ANetMor.f u ≈ ANetMor.f v
  ; id = record { f = id ; s-eqv = id-comm-sym ; t-eqv = id-comm-sym }
  ; _∘_ = comp
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where
  comp : {A B C : ANetObj} → ANetMor B C → ANetMor A B → ANetMor A C
  comp {A} {B} {C} (anetmor f eqs eqt) (anetmor g eqs' eqt') = anetmor (f ∘ g)
    (begin (f ∘ g) ∘ ANetObj.s A  ≈⟨ pullʳ eqs' ○ sym assoc ⟩
           (f ∘ ANetObj.s B) ∘ g  ≈⟨ pushˡ eqs ⟩
            ANetObj.s C ∘ f ∘ g   ∎)
    (begin (f ∘ g) ∘ ANetObj.t A  ≈⟨ pullʳ eqt' ○ sym assoc ⟩
           (f ∘ ANetObj.t B) ∘ g  ≈⟨ pushˡ eqt ⟩
            ANetObj.t C ∘ f ∘ g   ∎)


Graphs : Category _ _ _
Graphs = record
  { Obj = GraphObj
  ; _⇒_ = λ G H → GraphMor G H
  ; _≈_ = λ u v → (GraphMor.fE u ≈ GraphMor.fE v) × (GraphMor.fV u ≈ GraphMor.fV v)
  ; id = graphmor id id id-comm-sym id-comm-sym
  ; _∘_ = comp
  ; assoc = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv = record { refl = refl , refl ; sym = λ x → (sym (proj₁ x)) , (sym (proj₂ x)) ; trans = λ p q → (trans (proj₁ p) (proj₁ q)) , (trans (proj₂ p) (proj₂ q)) }
  ; ∘-resp-≈ = λ p q → (∘-resp-≈ (proj₁ p) (proj₁ q)) , (∘-resp-≈ (proj₂ p) (proj₂ q))
  }
  where
  comp : {A B C : GraphObj} → GraphMor B C → GraphMor A B → GraphMor A C
  comp {A} {B} {C} (graphmor fE fV eqs eqt) (graphmor gE gV eqs' eqt') = graphmor (fE ∘ gE) (fV ∘ gV)
    (begin (fV ∘ gV) ∘ s A ≈⟨ pullʳ eqs' ⟩
            fV ∘ s B ∘ gE  ≈⟨ pullˡ eqs ○ assoc ⟩
            s C ∘ fE ∘ gE  ∎)
    (begin (fV ∘ gV) ∘ t A ≈⟨ pullʳ eqt' ⟩
            fV ∘ t B ∘ gE  ≈⟨ pullˡ eqt ○ assoc ⟩
            t C ∘ fE ∘ gE  ∎)

-- a "tautological" functor aNets -> Graphs
q* : Functor aNets Graphs
q* = record
  { F₀ = λ {record { X = X ; s = s ; t = t } → record { s = s ; t = t }}
  ; F₁ = λ {(anetmor f seqv teqv) → graphmor f f seqv teqv}
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x , x
  }


-- a functor Graphs -> aNets, if the ambient category has coproducts
D : Cocartesian 𝒞 → Functor Graphs aNets
D coc = record
  { F₀ = λ {(graphobj {E} {V} s t) → anetobj {E + V} [ i₂ ∘ s , i₂ ] [ i₂ ∘ t , i₂ ]}
  ; F₁ = λ {(graphmor fE fV s-eqv t-eqv) → anetmor (fE +₁ fV) {!   !} {!   !}}
  ; identity = identity -+-
  ; homomorphism = homomorphism -+-
  ; F-resp-≈ = λ { {A} {B} {u} {v} (fst , snd) → F-resp-≈ -+- (fst , snd) }
  } where open Cocartesian coc
          open Functor

thm : {coc : Cocartesian 𝒞} → D coc ⊣ q*
thm = record
  { unit = {!   !}
  ; counit = {!   !}
  ; zig = {!   !}
  ; zag = {!   !}
  }