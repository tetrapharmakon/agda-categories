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
open import Categories.Category.Complete.Finitely ℂ
open import Categories.Diagram.Pullback
open import Categories.Category.Cocomplete.Finitely ℂ

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

-- another functor
-- R : {fc : FinitelyComplete} → Functor aNets Graphs
-- R {fc} = record
--   { F₀ = λ { (anetobj {X} s t) → graphobj {obj (equalizer fc s t)} {P (pullback fc s (arr (equalizer fc s t)))} {!   !} {!   !}}
--   ; F₁ = λ { {anetobj {A} s t} {anetobj {B} s' t'} (anetmor f s-eqv t-eqv) → graphmor (equalize ((equalizer fc s' t')) {!   !}) {!   !} {!   !} {!   !}}
--   ; identity = {!   !}
--   ; homomorphism = {!   !}
--   ; F-resp-≈ = {!   !}
--   } where open Equalizer
--           open FinitelyComplete
--           open Pullback

{-

E  ⇉ V  → π₀K = coequalizer.obj fcoc s t
↓    ↓     ↓
E' ⇉ V' → π₀K' = coequalizer.obj fcoc s' t'

-}

π₀ : {fcoc : FinitelyCocomplete} → Functor Graphs ℂ
π₀ {fcoc} = record
  { F₀ = λ { (graphobj s t) → coequalizer.obj s t}
  ; F₁ = λ { {graphobj {E} {V} s t} {graphobj {E'} {V'} s' t'} (graphmor fE fV s-eqv t-eqv) → coequalizer.coequalize s t
    (let eq-arr {s'} {t'} = coequalizer.arr s' t' in
      begin  (eq-arr ∘ fV) ∘ s  ≈⟨ assoc ⟩
             eq-arr ∘ fV ∘ s    ≈⟨ refl⟩∘⟨ s-eqv ⟩
             eq-arr ∘ s' ∘ fE   ≈⟨ sym assoc ⟩
             (eq-arr ∘ s') ∘ fE ≈⟨ equality (coequalizer s' t') ⟩∘⟨refl ⟩
             (eq-arr ∘ t') ∘ fE ≈⟨ assoc ⟩
             eq-arr ∘ t' ∘ fE   ≈⟨ (refl⟩∘⟨ sym t-eqv) ⟩
             eq-arr ∘ fV ∘ t    ≈⟨ sym assoc ⟩
             (eq-arr ∘ fV) ∘ t  ∎)}
  ; identity = λ { {graphobj {E} {V} s t} → sym (unique (coequalizer s t) id-comm) }
  ; homomorphism = λ { {graphobj {E} {V} s t} {graphobj {E'} {V'} s' t'} {graphobj {E''} {V''} s'' t''} {graphmor fE₁ fV₁ s-eqv₁ t-eqv₁} {graphmor fE₂ fV₂ s-eqv₂ t-eqv₂} → sym (unique (coequalizer s t)
    (let open module ST {f} {g} = Coequalizer (coequalizer f g)
         open module S'T' = Coequalizer (coequalizer s' t') in
      begin ST.arr ∘ fV₂ ∘ fV₁ ≈⟨ sym assoc ⟩
           (ST.arr ∘ fV₂) ∘ fV₁ ≈⟨ universal (coequalizer s' t') ⟩∘⟨refl ⟩
           ((S'T'.coequalize proof-eq) ∘ S'T'.arr) ∘ fV₁ ≈⟨ assoc ⟩
           (S'T'.coequalize proof-eq) ∘ S'T'.arr ∘ fV₁ ≈⟨ refl⟩∘⟨ universal (coequalizer s t) ⟩
           (S'T'.coequalize proof-eq) ∘ coequalizer.coequalize s t proof-eq ∘ coequalizer.arr s t ≈⟨ sym assoc ⟩
           ((S'T'.coequalize proof-eq) ∘ coequalizer.coequalize s t proof-eq) ∘ coequalizer.arr s t ∎))}
  ; F-resp-≈ = λ { {graphobj s t} (_ , snd) → coequalize-resp-≈ (coequalizer s t) (refl⟩∘⟨ snd)}
  } where open FinitelyCocomplete fcoc
          proof-eq : {X Y : Category.Obj Graphs} {f : GraphMor X Y} → (coequalizer.arr (s Y) (t Y) ∘ fV f) ∘ s X ≈ (coequalizer.arr (s Y) (t Y) ∘ fV f) ∘ t X
          proof-eq {graphobj {E} {V} s t} {graphobj {E'} {V'} s' t'} {graphmor fE₁ fV₁ s-eqv₁ t-eqv₁} =
            begin (arr ∘ fV₁) ∘ s ≈⟨ assoc ⟩
                  arr ∘ fV₁ ∘ s ≈⟨ (refl⟩∘⟨ s-eqv₁) ⟩
                  arr ∘ s' ∘ fE₁  ≈⟨ sym assoc ⟩
                  (arr ∘ s') ∘ fE₁  ≈⟨ equality ⟩∘⟨refl ⟩
                  (arr ∘ t') ∘ fE₁  ≈⟨ assoc ⟩
                  arr ∘ t' ∘ fE₁  ≈⟨ (refl⟩∘⟨ sym t-eqv₁) ⟩
                  arr ∘ fV₁ ∘ t ≈⟨ sym assoc ⟩
                  (arr ∘ fV₁) ∘ t ∎
              where
                open module M {f} {g} = Coequalizer (coequalizer f g)
          open Coequalizer

-- todo
-- define pi0
-- define triequaliser
