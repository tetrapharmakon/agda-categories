{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Data.Product

module ArrowNet {o ℓ e} (ℂ : Category o ℓ e) where

open Category ℂ
open HomReasoning
open Equiv

open import Level

open import Categories.Morphism.Reasoning ℂ
open import Categories.Functor.Core
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Category.Cartesian as c
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian as cc
open import Categories.Object.Coproduct
open import Categories.Adjoint
open import Categories.Functor.Limits
open import Categories.Diagram.Equalizer ℂ
open import Categories.Diagram.Coequalizer ℂ
open import Categories.Diagram.Pullback ℂ
open import Categories.Category.Complete.Finitely ℂ
open import Categories.Category.Cocomplete.Finitely ℂ

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
    s-eqv : fV ∘ G.s ≈ H.s ∘ fE
    t-eqv : fV ∘ G.t ≈ H.t ∘ fE

open GraphMor

record RGraphObj : Set (o ⊔ ℓ ⊔ e) where
  constructor rgraphobj
  field
    {E V} : Obj
    s t : E ⇒ V
    i : V ⇒ E
    eq-s : s ∘ i ≈ id
    eq-t : t ∘ i ≈ id

open RGraphObj

record RGraphMor (G H : RGraphObj) : Set (ℓ ⊔ e) where
  constructor rgraphmor
  private
    module G = RGraphObj G
    module H = RGraphObj H
  field
    fE : G.E ⇒ H.E
    fV : G.V ⇒ H.V
    s-eqv : fV ∘ G.s ≈ H.s ∘ fE
    t-eqv : fV ∘ G.t ≈ H.t ∘ fE

open RGraphMor

-- -- triqualizers
-- record IsTriqualizer {X Y obj E12 E23} (f g h : X ⇒ Y)
--   (e12 : E12 ⇒ X)
--   (e23 : E23 ⇒ X)
--   (p1 : obj ⇒ E12)
--   (p2 : obj ⇒ E23) : Set (o ⊔ ℓ ⊔ e) where
--   field
--     isEq-fg : IsEqualizer e12 f g
--     isEq-gh : IsEqualizer e23 g h
--     isPb    : IsPullback p1 p2 e12 e23

--   arr : obj ⇒ X
--   arr = e12 ∘ p1

-- record Triqualizer {X Y}  (f g h : X ⇒ Y) : Set (o ⊔ ℓ ⊔ e) where
--   field
--     {obj E12 E23} : Obj
--     e12 : E12 ⇒ X
--     e23 : E23 ⇒ X
--     p1 : obj ⇒ E12
--     p2 : obj ⇒ E23
--     isTriqualizer : IsTriqualizer f g h e12 e23 p1 p2

--   open IsTriqualizer isTriqualizer public

-- record IsTriback {X Y Z trg obj P12 P23}
--   (f : X ⇒ trg)
--   (g : Y ⇒ trg)
--   (h : Z ⇒ trg)
--   (p₁ : P12 ⇒ X) (p₂ : P12 ⇒ Y)
--   (q₁ : P23 ⇒ Y) (q₂ : P23 ⇒ Z)
--   (r₁ : obj ⇒ P12) (r₂ : obj ⇒ P23) : Set (o ⊔ ℓ ⊔ e) where
--   field
--     pb1 : IsPullback p₁ p₂ f g
--     pb2 : IsPullback q₁ q₂ g h
--     tripb : IsPullback r₁ r₂ p₂ q₁

--   arr : obj ⇒ Y
--   arr = p₂ ∘ r₁

-- record Triback {X Y Z trg}
--   (f : X ⇒ trg)
--   (g : Y ⇒ trg)
--   (h : Z ⇒ trg) : Set (o ⊔ ℓ ⊔ e) where
--   field
--     {obj P12 P23} : Obj
--     p₁ : P12 ⇒ X
--     p₂ : P12 ⇒ Y
--     q₁ : P23 ⇒ Y
--     q₂ : P23 ⇒ Z
--     r₁ : obj ⇒ P12
--     r₂ : obj ⇒ P23
--     isTriback : IsTriback f g h p₁ p₂ q₁ q₂ r₁ r₂

--   open IsTriback isTriback public

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

RGraphs : Category _ _ _
RGraphs = record
  { Obj = RGraphObj
  ; _⇒_ = λ G H → RGraphMor G H
  ; _≈_ = λ u v → (fE u ≈ fE v) × (fV u ≈ fV v)
  ; id = rgraphmor id id id-comm-sym id-comm-sym
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
  } where
      comp : {A B C : RGraphObj} → RGraphMor B C → RGraphMor A B → RGraphMor A C
      comp {A} {B} {C} (rgraphmor fE fV eqs eqt) (rgraphmor gE gV eqs' eqt') = rgraphmor (fE ∘ gE) (fV ∘ gV)
        (begin (fV ∘ gV) ∘ s A ≈⟨ pullʳ eqs' ⟩
                fV ∘ s B ∘ gE  ≈⟨ pullˡ eqs ○ assoc ⟩
                s C ∘ fE ∘ gE  ∎)
        (begin (fV ∘ gV) ∘ t A ≈⟨ pullʳ eqt' ⟩
                fV ∘ t B ∘ gE  ≈⟨ pullˡ eqt ○ assoc ⟩
                t C ∘ fE ∘ gE  ∎)

-- a "tautological" functor aNets -> Graphs
q* : Functor aNets Graphs
q* = record
  { F₀ = λ { (anetobj {X} s t) → graphobj s t}
  ; F₁ = λ {(anetmor f seqv teqv) → graphmor f f seqv teqv}
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x , x
  }

q0* : Functor aNets Graphs
q0* = record
  { F₀ = λ { (anetobj {X} _ _) → graphobj {X} {X} id id}
  ; F₁ = λ { (anetmor f _ _) → graphmor f f id-comm id-comm}
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x , x
  }

qs* : Functor aNets Graphs
qs* = record
  { F₀ = λ { (anetobj {X} s _) → graphobj {X} {X} s s}
  ; F₁ = λ { (anetmor f s-eqv _) → graphmor f f s-eqv s-eqv}
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x , x
  }

qt* : Functor aNets Graphs
qt* = record
  { F₀ = λ { (anetobj {X} _ t) → graphobj {X} {X} t t}
  ; F₁ = λ { (anetmor f _ t-eqv) → graphmor f f t-eqv t-eqv}
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x , x
  }

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

W : Cartesian ℂ → Functor Graphs aNets
W c = record
  { F₀ = λ {(graphobj {E} {V} s t) → anetobj {A×B} ⟨ π₁ , s ∘ π₁ ⟩ ⟨ π₁ , t ∘ π₁ ⟩}
  ; F₁ = λ { {graphobj s t} {graphobj s' t'} (graphmor fE fV s-eqv t-eqv) → anetmor (fE ⁂ fV)
      (begin ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩ ∘ ⟨ π₁ , s ∘ π₁ ⟩                       ≈⟨ ⟨⟩∘ ⟩
             ⟨ (fE ∘ π₁) ∘ ⟨ π₁ , s ∘ π₁ ⟩ , (fV ∘ π₂) ∘ ⟨ π₁ , s ∘ π₁ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (assoc ○ refl⟩∘⟨ project₁) (assoc ○ refl⟩∘⟨ project₂) ⟩
             ⟨ fE ∘ π₁ , fV ∘ s ∘ π₁ ⟩                                     ≈⟨ ⟨⟩-congˡ (sym assoc ○ (s-eqv ⟩∘⟨refl) ○ assoc) ⟩
             ⟨ fE ∘ π₁ , s' ∘ fE ∘ π₁ ⟩                                    ≈⟨ ⟨⟩-congʳ (introˡ refl) ⟩
             ⟨ id ∘ fE ∘ π₁ , s' ∘ fE ∘ π₁ ⟩                               ≈⟨ sym ⟨⟩∘ ⟩
             ⟨ id , s' ⟩ ∘ fE ∘ π₁                                         ≈⟨ refl⟩∘⟨ sym project₁ ⟩
             ⟨ id , s' ⟩ ∘ π₁ ∘ ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩                      ≈⟨ sym assoc ⟩
             (⟨ id , s' ⟩ ∘ π₁) ∘ ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩                    ≈⟨ (⟨⟩∘ ○ ⟨⟩-congʳ identityˡ) ⟩∘⟨refl ⟩
             ⟨ π₁ , s' ∘ π₁ ⟩ ∘ ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩                      ∎)
      (begin ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩ ∘ ⟨ π₁ , t ∘ π₁ ⟩                       ≈⟨ ⟨⟩∘ ⟩
             ⟨ (fE ∘ π₁) ∘ ⟨ π₁ , t ∘ π₁ ⟩ , (fV ∘ π₂) ∘ ⟨ π₁ , t ∘ π₁ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (assoc ○ refl⟩∘⟨ project₁) (assoc ○ refl⟩∘⟨ project₂) ⟩
             ⟨ fE ∘ π₁ , fV ∘ t ∘ π₁ ⟩                                     ≈⟨ ⟨⟩-congˡ (sym assoc ○ (t-eqv ⟩∘⟨refl) ○ assoc) ⟩
             ⟨ fE ∘ π₁ , t' ∘ fE ∘ π₁ ⟩                                    ≈⟨ ⟨⟩-congʳ (introˡ refl) ⟩
             ⟨ id ∘ fE ∘ π₁ , t' ∘ fE ∘ π₁ ⟩                               ≈⟨ sym ⟨⟩∘ ⟩
             ⟨ id , t' ⟩ ∘ fE ∘ π₁                                         ≈⟨ refl⟩∘⟨ sym project₁ ⟩
             ⟨ id , t' ⟩ ∘ π₁ ∘ ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩                      ≈⟨ sym assoc ⟩
             (⟨ id , t' ⟩ ∘ π₁) ∘ ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩                    ≈⟨ (⟨⟩∘ ○ ⟨⟩-congʳ identityˡ) ⟩∘⟨refl ⟩
             ⟨ π₁ , t' ∘ π₁ ⟩ ∘ ⟨ fE ∘ π₁ , fV ∘ π₂ ⟩                      ∎) }
  ; identity = identity -×-
  ; homomorphism = homomorphism -×-
  ; F-resp-≈ = λ { (fst , snd) → (F-resp-≈ -×-) (fst , snd) }
  } where open Cartesian c
          open BinaryProducts products
          open Functor

-- gives the object of vertices
forget : Functor aNets ℂ
forget = record
  { F₀ = λ { (anetobj {X} _ _) → X }
  ; F₁ = λ (anetmor f _ _) → f
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }

-- same, but for graphs
forget' : Functor Graphs ℂ
forget' = record
  { F₀ = λ { (graphobj {_} {V} _ _) → V }
  ; F₁ = λ { (graphmor _ fV _ _) → fV }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ { (_ , snd) → snd }
  }

-- the discrete graph on a set: Ø ⇉ S
disc : Cocartesian ℂ → Functor ℂ Graphs
disc coc = record
  { F₀ = λ S → graphobj {_} {S} ¡ ¡
  ; F₁ = λ u → graphmor id u (¡-unique₂ (u ∘ ¡) (¡ ∘ id)) (¡-unique₂ (u ∘ ¡) (¡ ∘ id))
  ; identity = refl , refl
  ; homomorphism = sym identity² , refl
  ; F-resp-≈ = λ x → refl , x
  } where open Cocartesian coc
          open Functor

-- the graph with a single loop for every vertex in a set S
loop : Functor ℂ Graphs
loop = record
  { F₀ = λ S → graphobj {S} {S} id id
  ; F₁ = λ u → graphmor u u id-comm id-comm
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ x → x , x
  }

-- the codiscrete graph on a set: S × S ⇉ S
codisc : Cartesian ℂ → Functor ℂ Graphs
codisc c = record
  { F₀ = λ S → graphobj {A×B} {S} π₁ π₂
  ; F₁ = λ u → graphmor (u ⁂ u) u (sym π₁∘⁂) (sym π₂∘⁂)
  ; identity = (⟨⟩-cong₂ identityˡ identityˡ ○ η) , refl
  ; homomorphism = sym ⁂∘⁂ , refl
  ; F-resp-≈ = λ u≈v → ⁂-cong₂ u≈v u≈v , u≈v
  } where open Cartesian c
          open Functor
          open BinaryProducts products

π₀ : {fcoc : FinitelyCocomplete} → Functor Graphs ℂ
π₀ {fcoc} = record
  { F₀ = λ { (graphobj s t) → coequalizer.obj s t}
  ; F₁ = λ { {graphobj s t} {graphobj s' t'} (graphmor fE fV s-eqv t-eqv) → coequalizer.coequalize s t
    (let open module S'T' = Coequalizer (coequalizer s' t') in
     begin (S'T'.arr ∘ fV) ∘ s  ≈⟨ pullʳ s-eqv ⟩
           S'T'.arr ∘ s' ∘ fE   ≈⟨ pullˡ (equality (coequalizer s' t')) ⟩
           (S'T'.arr ∘ t') ∘ fE ≈⟨ pullʳ (sym t-eqv) ○ sym assoc ⟩
           (S'T'.arr ∘ fV) ∘ t  ∎) }
  ; identity = λ { {graphobj s t} → sym (unique (coequalizer s t) id-comm) }
  ; homomorphism = λ { {graphobj s t} {graphobj s' t'} {graphobj s'' t''} {graphmor _ fV₁ _ _} {graphmor _ fV₂ _ _} →
      sym (unique (coequalizer s t)
        (let open module ST     = Coequalizer (coequalizer s t)
             open module S'T'   = Coequalizer (coequalizer s' t')
             open module S''T'' = Coequalizer (coequalizer s'' t'') in
          begin S''T''.arr ∘ fV₂ ∘ fV₁                                      ≈⟨ pullˡ S'T'.universal ⟩
               (S'T'.coequalize proof-eq ∘ S'T'.arr) ∘ fV₁                  ≈⟨ pullʳ ST.universal ○ sym assoc ⟩
               (S'T'.coequalize proof-eq ∘ ST.coequalize proof-eq) ∘ ST.arr ∎))
              }
  ; F-resp-≈ =
    λ { {graphobj s t} (_ , snd) →
     let open module ST = Coequalizer (coequalizer s t) in
       ST.coequalize-resp-≈ (refl⟩∘⟨ snd)
    }
  } where open FinitelyCocomplete fcoc
          proof-eq : ∀ {X Y} {f : GraphMor X Y} →
            (coequalizer.arr (s Y) (t Y) ∘ fV f) ∘ s X ≈ (coequalizer.arr (s Y) (t Y) ∘ fV f) ∘ t X
          proof-eq {graphobj s t} {graphobj s' t'} {graphmor fE fV s-eqv t-eqv} =
            begin (arr ∘ fV) ∘ s  ≈⟨ pullʳ s-eqv ⟩
                   arr ∘ s' ∘ fE  ≈⟨ pullˡ equality ⟩
                  (arr ∘ t') ∘ fE ≈⟨ pullʳ (sym t-eqv) ○ sym assoc ⟩
                  (arr ∘ fV) ∘ t  ∎
              where open module M {f} {g} = Coequalizer (coequalizer f g)
          open Coequalizer

j : Functor RGraphs Graphs
j = record
  { F₀ = λ {(rgraphobj s t i eq-s eq-t) → graphobj s t}
  ; F₁ = λ {(rgraphmor fE fV s-eqv t-eqv) → graphmor fE fV s-eqv t-eqv}
  ; identity = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈ = λ (fst , snd) → fst , snd
  }

R : {coc : Cocartesian ℂ} → Functor Graphs RGraphs
R {coc} = record
  { F₀ = λ {(graphobj {E} {V} s t) → rgraphobj {V + E} {V} [ id , s ] [ id , t ] i₁ inject₁ inject₁}
  ; F₁ = λ { {graphobj s t} {graphobj s' t'} (graphmor fE fV s-eqv t-eqv) → rgraphmor (fV +₁ fE) fV
          (begin fV ∘ [ id , s ]                                     ≈⟨ ∘-distribˡ-[] ⟩
                 [ fV ∘ id , fV ∘ s ]                                ≈⟨ []-cong₂ id-comm s-eqv ⟩
                 [ id  ∘ fV , s' ∘ fE ]                              ≈⟨ []-cong₂ (pushˡ (sym inject₁)) (pushˡ (sym inject₂)) ⟩
                 [ [ id , s' ] ∘ i₁  ∘ fV , [ id , s' ] ∘ i₂  ∘ fE ] ≈⟨ sym ∘-distribˡ-[] ⟩
                 [ id , s' ] ∘ [ i₁  ∘ fV , i₂  ∘ fE ]               ∎)
         (begin fV ∘ [ id , t ] ≈⟨ ∘-distribˡ-[] ⟩
                 [ fV ∘ id , fV ∘ t ]                                ≈⟨ []-cong₂ id-comm t-eqv ⟩
                 [ id  ∘ fV , t' ∘ fE ]                              ≈⟨ []-cong₂ (pushˡ (sym inject₁)) (pushˡ (sym inject₂)) ⟩
                 [ [ id , t' ] ∘ i₁  ∘ fV , [ id , t' ] ∘ i₂  ∘ fE ] ≈⟨ sym ∘-distribˡ-[] ⟩
                 [ id , t' ] ∘ [ i₁  ∘ fV , i₂  ∘ fE ]               ∎)}
  ; identity = ([]-cong₂ identityʳ identityʳ ○ +-η) , refl
  ; homomorphism = λ {
    {_} {_} {_} {graphmor fE fV _ _} {graphmor fE' fV' _ _} →
      sym (begin [ i₁ ∘ fV' , i₂ ∘ fE' ] ∘ [ i₁ ∘ fV , i₂ ∘ fE ]                           ≈⟨ ∘-distribˡ-[] ⟩
                 [ [ i₁ ∘ fV' , i₂ ∘ fE' ] ∘ i₁ ∘ fV , [ i₁ ∘ fV' , i₂ ∘ fE' ] ∘ i₂ ∘ fE ] ≈⟨ []-cong₂ (pullˡ inject₁ ○ assoc) (pullˡ inject₂ ○ assoc) ⟩
                 [ i₁ ∘ fV' ∘ fV , i₂ ∘ fE' ∘ fE ]                                         ∎)
      , refl}
  ; F-resp-≈ = λ {(fst , snd) → ([]-cong₂ (refl⟩∘⟨ snd) (refl⟩∘⟨ fst)) , snd}
  } where open Cocartesian coc

-- various adjunctions
disc⊣forget : {coc : Cocartesian ℂ} → disc coc ⊣ forget'
disc⊣forget {coc} = record
  { unit = record
    { η = λ _ → id
    ; commute = λ _ → id-comm-sym
    ; sym-commute = λ _ → id-comm
    }
  ; counit = record
    { η = λ { (graphobj {E} {V} s t) → graphmor ¡ id (¡-unique₂ (id ∘ ¡) (s ∘ ¡)) (¡-unique₂ (id ∘ ¡) (t ∘ ¡)) }
    ; commute = λ { (graphmor fE fV s-eqv t-eqv) → trans identityʳ (¡-unique _) , id-comm-sym }
    ; sym-commute = λ f → trans (sym (¡-unique _)) (sym identityʳ) , id-comm
    }
  ; zig = ⊥-id (¡ ∘ id) , identity²
  ; zag = identity²
  } where open Cocartesian coc
          open Functor

forget⊣codisc : {c : Cartesian ℂ} → forget' ⊣ codisc c
forget⊣codisc {c} = record
  { unit = record
    { η = λ { (graphobj s t) → graphmor ⟨ s , t ⟩ id (sym (project₁ ○ sym identityˡ)) (sym (project₂ ○ sym identityˡ)) }
    ; commute = λ { {graphobj s t} {graphobj s' t'} (graphmor fE fV s-eqv t-eqv) →
      (begin
        ⟨ s' , t' ⟩ ∘ fE                  ≈⟨ ⟨⟩∘ ⟩
        ⟨ s' ∘ fE , t' ∘ fE  ⟩            ≈⟨ sym (⟨⟩-cong₂ s-eqv t-eqv) ⟩
        ⟨ fV ∘ s , fV ∘ t ⟩               ≈⟨ sym ⁂∘⟨⟩ ⟩
        ⟨ fV ∘ π₁ , fV ∘ π₂ ⟩ ∘ ⟨ s , t ⟩ ∎)
      , id-comm-sym }
    ; sym-commute = λ { {graphobj s t} {graphobj s' t'} (graphmor fE fV s-eqv t-eqv) →
      sym (begin
             ⟨ s' , t' ⟩ ∘ fE                  ≈⟨ ⟨⟩∘ ⟩
             ⟨ s' ∘ fE , t' ∘ fE  ⟩            ≈⟨ sym (⟨⟩-cong₂ s-eqv t-eqv) ⟩
             ⟨ fV ∘ s , fV ∘ t ⟩               ≈⟨ sym ⁂∘⟨⟩ ⟩
             ⟨ fV ∘ π₁ , fV ∘ π₂ ⟩ ∘ ⟨ s , t ⟩ ∎)
      , id-comm }
    }
  ; counit = record
    { η = λ { _ → id }
    ; commute = λ _ → id-comm-sym
    ; sym-commute = λ _ → id-comm
    }
  ; zig = identity²
  ; zag =
    (begin
      ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ π₁ , π₂ ⟩ ≈⟨ refl⟩∘⟨ η ⟩
      ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ∘ id          ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩∘⟨refl ⟩
      ⟨ π₁ , π₂ ⟩ ∘ id                    ≈⟨ η ⟩∘⟨refl ○ identity² ⟩
      id                                  ∎)
    , identity²
  } where open Cartesian c
          open Functor
          open BinaryProducts products


j⊣R : {coc : Cocartesian ℂ} → j ⊣ R {coc}
j⊣R {coc} = record
  { unit = record
    { η = λ _ → rgraphmor i₂ id (trans identityˡ (sym inject₂)) (trans identityˡ (sym inject₂))
    ; commute = λ _ → sym inject₂ , sym id-comm
    ; sym-commute = λ _ → inject₂ , id-comm
    }
  ; counit = record
    { η = {!   !} -- wtf λ {(graphobj {E} {V} s t) → graphmor [ i (Functor.F₀ R (graphobj s t)) , id ] id {!   !} {!   !}}
    ; commute = {!   !}
    ; sym-commute = {!   !}
    }
  ; zig = {!   !}
  ; zag = {!   !}
  } where open Cocartesian coc