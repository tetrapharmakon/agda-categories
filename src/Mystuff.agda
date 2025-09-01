
module Mystuff where

-- open import Axiom.Extensionality.Propositional as AEP
open import Categories.Category.Cartesian.Bundle
open import Categories.Category.CartesianClosed.Canonical
open import Categories.Category.Core
open import Categories.Category.Slice
-- open import Categories.Functor
open import Categories.Category.BinaryProducts
-- open import Categories.Morphism
open import Categories.Object.Exponential -- 𝒞 hiding (repack)
open import Data.Product
open import Function using (const)
open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

private
  variable
    a b c d e : Level

-- so painful
_⋆_ : ∀ {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ⋆ g = λ x → f (g x)

simple : Category (suc zero) zero zero
simple =
 record
  -- structure
  { Obj = Set × Set
  ; _⇒_ = _⇒_
  ; _≈_ = _≡_
  ; id  = (λ z → z) , proj₁
  ; _∘_ = _∘_
  -- properties
  ; assoc     = refl
  ; sym-assoc = refl
  ; identityˡ  = refl
  ; identityʳ  = refl
  ; identity² = refl
  -- whew, they're all trivial!
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp
  }
  where
  _⇒_ : Rel (Set × Set) zero
  (i , x) ⇒ (j , y) = (i → j) × (x × i → y)
  _∘_ : {A B C : Set × Set} → B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ {i , x} {j , y} {_} (u , f) (v , g) =
   (λ t → u (v t)) , λ t → f (g t , v (proj₂ t))
  ∘-resp :
    {A B C : Set × Set} {f h : B ⇒ C} {g i : A ⇒ B} →
    --------------------------------------------------
    f ≡ h → g ≡ i → (f ∘ g) ≡ (h ∘ i)
  ∘-resp {A} {B} {C} {f} {h} {g} {i} x y =
   trans (cong (λ t → t ∘ g) x) (cong (λ t → h ∘ t) y)

data t : Set where
 ⊤ : t

!-unique-lemma : ∀ (x : t) → ⊤ ≡ x
!-unique-lemma ⊤ = refl

postulate
 -- I'm lazy.
 respSetC : {A B C : Set} {f h : B → C} {g i : A → B} →
  f ≡ h →
  g ≡ i →
  (λ a → f (g a)) ≡ (λ a → h (i a))
 extensionality : ∀ {A B : Set} {f g : A → B} →
  (∀ (x : A) → f x ≡ g x) →
  f ≡ g

-- I need the category of Sets...
SetC : Category (suc zero) zero zero
SetC =
 record
  { Obj = Set
  ; _⇒_ = λ x y → x → y
  ; _≈_ = _≡_
  ; id = λ x → x
  ; _∘_ = λ f g a → f (g a)
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = respSetC
  }

_·_ : {I : Set} {A B C : Set} → (B × I → C) → (A × I → B) → A × I → C
_·_ {I} f g (x , i) = f (g(x , i) , i)

fiber-of-simple : {I : Set} → Category (suc zero) zero zero
fiber-of-simple {I} =
 record
  { Obj = Set
  ; _⇒_ = λ X Y → X × I → Y
  ; _≈_ = _≡_
  ; id  = proj₁
  ; _∘_ = _·_ -- this is the Kleisli composition
  ; assoc     = refl
  ; sym-assoc = refl
  ; identityˡ  = refl
  ; identityʳ  = refl
  ; identity² = refl
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = rresp
  }
  where
  rresp : {A B C : Set} {f h : B × I → C} {g i : A × I → B} → f ≡ h → g ≡ i → (f · g) ≡ (h · i)
  rresp {A} {B} {C} {f} {h} {g} {i} x y = trans (cong (λ t → t · g) x) (cong (_·_ h) y)

-- each fiber of a simple fibration is cartesian
fiber-of-simple-cart : ∀ {I : Set} → CartesianCategory (suc zero) zero zero
fiber-of-simple-cart {I} =
 record
  { U = fiber-of-simple {I}
  ; cartesian =
    record
     { terminal =
       record { ⊤ = t
           ; ⊤-is-terminal =
             record
              { ! = const ⊤
              ; !-unique =
                λ f → extensionality (λ x → !-unique-lemma (f x))
              }
           }
     ; products =
       record
        { product = λ {A} {B} →
          record
           { A×B = A × B
           ; π₁ = λ x → proj₁ (proj₁ x)
           ; π₂ = λ x → proj₂ (proj₁ x)
           ; ⟨_,_⟩ = λ f g t → f t , g t
           ; project₁ = refl
           ; project₂ = refl
           ; unique = λ {refl refl → refl}
           } } } }

-- but also the total category is cartesian.
simple-cart : CartesianCategory (suc zero) zero zero
simple-cart = record
 { U = simple
 ; cartesian = record
   { terminal = record { ⊤ = t , t
                       ; ⊤-is-terminal =
                         record { ! = const ⊤ , const ⊤
                                ; !-unique = bang-uniq
                                } }
   ; products = record { product = λ {A} {B} → record
              { A×B = (proj₁ A × proj₁ B) , (proj₂ A × proj₂ B)
              ; π₁ = proj₁ , λ x → proj₁ (proj₁ x)
              ; π₂ = proj₂ , (λ x → proj₂ (proj₁ x))
              ; ⟨_,_⟩ = ⟨_,_⟩
              ; project₁ = refl
              ; project₂ = refl
              ; unique = λ {refl refl → refl}
              } } } }
              where
               bang-uniq :
                {A : Category.Obj simple}
                -------------------------
                (f : (simple Category.⇒ A) (t , t)) →
                --------------------------------------
                (simple Category.≈ (const ⊤ , const ⊤)) f
               bang-uniq {I , X} (u , k) =
                cong₂ Data.Product._,_
                 (extensionality (λ x → !-unique-lemma (u x)))
                 (extensionality (λ x → !-unique-lemma (k x)))
               ⟨_,_⟩ :
                {A B C : Set × Set} →
                (simple Category.⇒ C) A →
                (simple Category.⇒ C) B →
                (simple Category.⇒ C) ((proj₁ A × proj₁ B) , (proj₂ A × proj₂ B))
               ⟨_,_⟩ {A0 , A1} {B0 , B1} {C0 , C1} (u , h) (v , k) =
                (λ x → (u x) , (v x)) , λ x → (h x) , (k x)

fib-of-simple-ccc : {I : Set} → CartesianClosed (fiber-of-simple {I})
fib-of-simple-ccc {I} =
 record
  { ⊤ = t
  ; _×_ = _×_
  ; ! = λ x → ⊤
  ; π₁ = proj₁ ⋆ proj₁
  ; π₂ = proj₂ ⋆ proj₁
  ; ⟨_,_⟩ = λ f g ci → (f ci) , (g ci)
  ; !-unique = λ f → extensionality λ x → !-unique-lemma (f x)
  ; π₁-comp = refl
  ; π₂-comp = refl
  ; ⟨,⟩-unique = λ {refl refl → refl}
  ; _^_ = λ A B → B → A
  ; eval = evev
  ; curry = λ f ci a → f (((proj₁ ci) , a) , (proj₂ ci))
  ; eval-comp = refl
  ; curry-resp-≈ = λ {refl → refl}
  ; curry-unique = λ {refl → refl}
  }
  where
  evev : {B A : Category.Obj (fiber-of-simple {I})} → (fiber-of-simple {I} Category.⇒ ((A → B) × A)) B
  evev ((f , a) , i) = f a

{-
the arrow category has objects the morphisms of `Set` and
morphisms the commutative squares

A → B
↓   ↓
C → D
-}
arrow : Category (suc zero) zero zero
arrow = record
  { Obj = Σ (Set × Set) (λ x → proj₁ x → proj₂ x)
  ; _⇒_ = arr
  ; _≈_ = _≡_
  ; id = (λ z → z) , λ z → z
  ; _∘_ = λ {A} {B} {C} f g → comp {A} {B} {C} f g
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ {refl refl → refl}
  }
  where
  arr : Rel (Σ (Set × Set) (λ x → proj₁ x → proj₂ x)) zero
  arr ((a , b) , x1) ((c , d) , y1) = (a → c) × (b → d)
  comp : {A B C : Σ (Set × Set) (λ x → proj₁ x → proj₂ x)} → arr B C → arr A B → arr A C
  comp {A} {B} {C} (f0 , f1) (g0 , g1) = (λ x → f0 (g0 x)) , λ x → f1 (g1 x)

arrow-ccc : CartesianClosed arrow
arrow-ccc = record
 { ⊤ = (t , t) , (λ _ → ⊤)
 ; _×_ = prod
 ; ! = (λ _ → ⊤) , (λ _ → ⊤)
 ; π₁ = proj₁ , proj₁
 ; π₂ = proj₂ , proj₂
 ; ⟨_,_⟩ = λ {A} {B} {C} f g → pair {A} {B} {C} f g
 ; !-unique = λ {A} → bang-uniq {A}
 ; π₁-comp = refl
 ; π₂-comp = refl
 ; ⟨,⟩-unique = λ {refl refl → refl}
 ; _^_ = to-the
 ; eval = λ {B} {A} → ev {B} {A}
 ; curry = λ {C} {A} {B} x → cur {C} {A} {B} x
 ; eval-comp = refl
 ; curry-resp-≈ = λ {refl → refl}
 ; curry-unique = {!   !}
 }
 where
 prod : Category.Obj arrow → Category.Obj arrow → Category.Obj arrow
 prod ((X , Y) , u) ((A , B) , v) =
  ((X × A) , (Y × B)) , λ x → (u (proj₁ x)) , (v (proj₂ x))
 pair : {C A B : Category.Obj arrow} →
  (arrow Category.⇒ C) A →
  (arrow Category.⇒ C) B →
  (arrow Category.⇒ C) (prod A B)
 pair {(X , Y) , u} {(A , B) , v} {(E , F) , w} (f0 , f1) (g0 , g1) =
  (λ x → (f0 x) , (g0 x)) , (λ x → (f1 x) , (g1 x))
 bang-uniq : {A : Category.Obj arrow} →
  (f : (arrow Category.⇒ A) ((t , t) , (λ _ → ⊤))) →
  ((λ _ → ⊤) , (λ _ → ⊤)) ≡ f
 bang-uniq (f0 , f1) =
  cong₂ _,_
   (extensionality λ x → !-unique-lemma (f0 x))
   (extensionality (λ x → !-unique-lemma (f1 x)))
 to-the : Category.Obj arrow →
  Category.Obj arrow →
  Category.Obj arrow
 to-the ((B0 , B1) , u) ((A0 , A1) , v) =
  (p , (A1 → B1)) , (λ x a1 → proj₂ (proj₁ x) a1)
   where
   p : Set
   p = Σ ((A0 → B0) × (A1 → B1)) (λ r → (λ x → u ((proj₁ r) x)) ≡ (λ x → (proj₂ r) (v x)))
 -- ^ it's the pullback-hom
 -- λ x → u (s x) ≡ λ x → t (v x)
 ev : {B A : Category.Obj arrow} → (arrow Category.⇒ prod (to-the B A) A) B
 ev {(B0 , B1) , u} {(A0 , A1)  , v} = dis , dat
  where
  dis : proj₁ (proj₁ (prod (to-the ((B0 , B1) , u) ((A0 , A1) , v)) ((A0 , A1) , v))) → B0
  dis ((d , p) , a0) = (proj₁ d) a0
  dat : proj₂ (proj₁ (prod (to-the ((B0 , B1) , u) ((A0 , A1) , v)) ((A0 , A1) , v))) → B1
  dat (fst , snd) = fst snd
 cur : {C A B : Category.Obj arrow} →
  (arrow Category.⇒ (prod C A)) B →
  (arrow Category.⇒ C) (to-the B A)
 cur {(C0 , C1) , u} {(A0 , A1) , v} {(B0 , B1) , w} (fst , snd) =
  (λ x → ((λ t → fst (x , t)) , λ t → snd (u x , t)) , extensionality (λ a0 → {!   !})) , (λ z z₁ → snd (z , z₁))