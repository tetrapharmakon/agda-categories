{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Data.Product

module ArrowNet {o ℓ e} (ℂ : Category o ℓ e) where

open Category ℂ
open HomReasoning
open Equiv

open import Level

open import Categories.Adjoint
open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian as c
open import Categories.Category.Cocartesian as cc
open import Categories.Category.Cocomplete.Finitely ℂ
open import Categories.Category.Complete.Finitely ℂ
open import Categories.Diagram.Coequalizer ℂ
open import Categories.Diagram.Equalizer ℂ
open import Categories.Diagram.Pullback ℂ
open import Categories.Functor.Core
open import Categories.Morphism.Reasoning ℂ
open import Categories.Object.Coproduct


{-
CATEGORIES
===
arrow network; an arrow network is a set equipped with an action
of the free monoid on two generators, called s,t to make evident
that an arrow network is also a special kind of graph (where the
object of vertices and of edges coincide).
-}
record ANetObj : Set (o ⊔ ℓ) where
  constructor anetobj
  field
    {X} : Obj
    s t : X ⇒ X

open ANetObj

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

record GraphObj : Set (o ⊔ ℓ) where
  constructor graphobj
  field
    {E V} : Obj
    s t : E ⇒ V

open GraphObj

record GraphMor (G H : GraphObj) : Set (ℓ ⊔ e) where
  constructor graphmor
  private
    module G = GraphObj G
    module H = GraphObj H
  field
    fE : G.E ⇒ H.E
    fV : G.V ⇒ H.V
    --
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
    (begin (f ∘ g) ∘ s A  ≈⟨ pullʳ eqs' ○ sym assoc ⟩
           (f ∘ s B) ∘ g  ≈⟨ pushˡ eqs ⟩
           s C ∘ f ∘ g    ∎)
    (begin (f ∘ g) ∘ t A  ≈⟨ pullʳ eqt' ○ sym assoc ⟩
           (f ∘ t B) ∘ g  ≈⟨ pushˡ eqt ⟩
           t C ∘ f ∘ g    ∎)

Graphs : Category _ _ _
Graphs = record
  { Obj = GraphObj
  ; _⇒_ = λ G H → GraphMor G H
  ; _≈_ = λ u v → (fE u ≈ fE v) × (fV u ≈ fV v)
  ; id = graphmor id id id-comm-sym id-comm-sym
  ; _∘_ = comp
  ; assoc = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv = record
    { refl = refl , refl
    ; sym = λ x → (sym (proj₁ x)) , (sym (proj₂ x))
    ; trans = λ p q → (trans (proj₁ p) (proj₁ q)) , (trans (proj₂ p) (proj₂ q))
    }
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

-- a functor Graphs -> aNets, if the ambient category has coproducts
D : Cocartesian ℂ → Functor Graphs aNets
D coc = record
  { F₀ = λ {(graphobj {E} {V} s t) → anetobj {E + V} [ i₂ ∘ s , i₂ ] [ i₂ ∘ t , i₂ ]}
  ; F₁ = λ { {A} {B} (graphmor fE fV s-eqv t-eqv) → anetmor (fE +₁ fV)
    (begin [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ [ i₂ ∘ s A , i₂ ]                            ≈⟨ ∘-distribˡ-[] ⟩
           [ [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂ ∘ s A , [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂ ]   ≈⟨ []-congʳ (sym assoc) ⟩
           [ ([ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂) ∘ s A , [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂ ] ≈⟨ []-cong₂ (inject₂ ⟩∘⟨refl) inject₂ ⟩
           [ (i₂ ∘ fV) ∘ s A ,  i₂ ∘ fV ]                                        ≈⟨ []-congʳ (pullʳ s-eqv ○ sym assoc) ⟩
           [ (i₂ ∘ s B) ∘ fE ,  i₂ ∘ fV ]                                        ≈⟨ []-cong₂ (sym (inject₁ ⟩∘⟨refl) ○ assoc) (sym (inject₂ ⟩∘⟨refl) ○ assoc) ⟩
           [ [ i₂ ∘ s B , i₂ ] ∘ i₁ ∘ fE ,  [ i₂ ∘ s B , i₂ ] ∘ i₂ ∘ fV ]        ≈⟨ sym ∘-distribˡ-[] ⟩
           [ i₂ ∘ s B , i₂ ] ∘ [ i₁ ∘ fE ,  i₂ ∘ fV ] ∎)
    (begin [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ [ i₂ ∘ t A , i₂ ]                            ≈⟨ ∘-distribˡ-[] ⟩
           [ [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂ ∘ t A , [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂ ]   ≈⟨ []-congʳ (sym assoc) ⟩
           [ ([ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂) ∘ t A , [ i₁ ∘ fE ,  i₂ ∘ fV ] ∘ i₂ ] ≈⟨ []-cong₂ (inject₂ ⟩∘⟨refl) inject₂ ⟩
           [ (i₂ ∘ fV) ∘ t A ,  i₂ ∘ fV ]                                        ≈⟨ []-congʳ (pullʳ t-eqv ○ sym assoc) ⟩
           [ (i₂ ∘ t B) ∘ fE ,  i₂ ∘ fV ]                                        ≈⟨ []-cong₂ (sym (inject₁ ⟩∘⟨refl) ○ assoc) (sym (inject₂ ⟩∘⟨refl) ○ assoc) ⟩
           [ [ i₂ ∘ t B , i₂ ] ∘ i₁ ∘ fE ,  [ i₂ ∘ t B , i₂ ] ∘ i₂ ∘ fV ]        ≈⟨ sym ∘-distribˡ-[] ⟩
           [ i₂ ∘ t B , i₂ ] ∘ [ i₁ ∘ fE ,  i₂ ∘ fV ] ∎)}
  ; identity = identity -+-
  ; homomorphism = homomorphism -+-
  ; F-resp-≈ = λ { (fst , snd) → F-resp-≈ -+- (fst , snd) }
  } where open Cocartesian coc
          open Functor

-- triqualizers
record IsTriqualizer {X Y obj E12 E23} (f g h : X ⇒ Y)
  (e12 : E12 ⇒ X)
  (e23 : E23 ⇒ X)
  (p1 : obj ⇒ E12)
  (p2 : obj ⇒ E23) : Set (o ⊔ ℓ ⊔ e) where
  field
    isEq-fg : IsEqualizer e12 f g
    isEq-gh : IsEqualizer e23 g h
    isPb    : IsPullback p1 p2 e12 e23

  arr : obj ⇒ X
  arr = e12 ∘ p1

record Triqualizer {X Y}  (f g h : X ⇒ Y) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj E12 E23} : Obj
    e12 : E12 ⇒ X
    e23 : E23 ⇒ X
    p1 : obj ⇒ E12
    p2 : obj ⇒ E23
    isTriqualizer : IsTriqualizer f g h e12 e23 p1 p2

  open IsTriqualizer isTriqualizer public

-- R : {fc : FinitelyComplete} → Functor aNets Graphs
-- R {fc} = record
--   { F₀ = λ {(anetobj {X} s t) → graphobj {FinitelyComplete.pullback.obj {!   !} {!   !}} {{!   !}} {!   !} {!   !}}
--   ; F₁ = {!   !}
--   ; identity = {!   !}
--   ; homomorphism = {!   !}
--   ; F-resp-≈ = {!   !}
--   } where open FinitelyComplete fc
--           -- open Triqualizer
--           -- open module P = Pullback (pullback (s BinaryProducts.⁂ t) s)

-- D⊣R : {coc : Cocartesian ℂ} → D coc ⊣ R
-- D⊣R {coc} = record
--   { unit = {!   !}
--   ; counit = {!   !}
--   ; zig = {!   !}
--   ; zag = {!   !}
--   } where open Cocartesian coc