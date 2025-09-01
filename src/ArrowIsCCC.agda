module ArrowIsCCC where

open import Categories.Category.CartesianClosed.Canonical
open import Categories.Category.Cartesian.Bundle
open import Categories.Category.Core
open import Categories.Category.Construction.Arrow
open import Data.Product
open import Function using (const)
open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

𝕦 : {A : Set} → A → A
𝕦 x = x

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
  ; ∘-resp-≈ = λ {refl refl → refl}
  }

data t : Set where
 ⊤ : t

!-unique-lemma : ∀ (x : t) → ⊤ ≡ x
!-unique-lemma ⊤ = refl


Set² : Category (suc zero) zero zero
Set² = Arrow SetC

arrow-cart : CartesianCategory (suc zero) zero zero
arrow-cart =
 record { U = Set²
        ; cartesian =
          record { terminal = record { ⊤ = record { arr = 𝕦 } ; ⊤-is-terminal = record { ! = mor⇒ {!   !} ; !-unique = {!   !} } }
                 ; products =
                   record { product = λ {A} {B} →
                    record
                     { A×B = record { arr = λ x → {!   !} }
                     ; π₁ = mor⇒ {!   !}
                     ; π₂ = mor⇒ {!   !}
                     ; ⟨_,_⟩ = λ x x₁ → {!   !}
                     ; project₁ = {!   !} , {!   !}
                     ; project₂ = {!   !} , {!   !}
                     ; unique = λ x x₁ → {!   !}
                     } } } }


{-
_⋆_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ⋆ f = λ t → g (f t)




postulate
 extensionality : ∀ {A B : Set} {f g : A → B} →
  (∀ (x : A) → f x ≡ g x) →
  f ≡ g

data t : Set where
 ⊤ : t

!-unique-lemma : ∀ (x : t) → ⊤ ≡ x
!-unique-lemma ⊤ = refl

arrow : Category (suc zero) zero zero
arrow = record
  { Obj = Σ (Set × Set) (λ x → proj₁ x → proj₂ x)
  ; _⇒_ = arr
  ; _≈_ = _≡_
  ; id = ((λ x → x) , (λ z → z)) , refl
  ; _∘_ = λ {A} {B} {C} f g → comp {A} {B} {C} f g
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = λ {A} {B} {f} → idl {A} {B} {f}
  ; identityʳ = λ {A} {B} {f} → idr {A} {B} {f}
  ; identity² = refl
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = λ {refl refl → refl}
  }
  where
  comm-sq : {a b c d : Set} → (a → c) × (b → d) → (f : a → b) → (g : c → d) → Set
  comm-sq {a} {b} {c} {d} (up , down) left right = ∀ {t : a} → down (left t) ≡ right (up t)
  arr : Rel (Σ (Set × Set) (λ x → proj₁ x → proj₂ x)) zero
  arr ((a , b) , x1) ((c , d) , y1) = Σ ((a → c) × (b → d)) λ x → comm-sq x x1 y1
  trans-comm-sq :
   {A B C X Y Z : Set} {up : A → B} {down : X → Y} {up' : B → C} {down' : Y → Z} {left : A → X} {right : B → Y} {right' : C → Z} →
   (p : comm-sq (up , down) left right) → (q : comm-sq (up' , down') right right') →
    comm-sq (up' ⋆ up , down' ⋆ down) left right'
  trans-comm-sq
   {A} {B} {C} {X} {Y} {Z} {up} {down} {up'} {down'} {left} {right} {right'}
   p q {t} =
    begin
     down' (down (left t)) ≡⟨ cong down' p ⟩
     down' (right (up t))  ≡⟨ q ⟩
     right' (up' (up t))
    ∎
  {-
    up   up'
  A -> B -> C
  ↓    ↓    ↓
  X -> Y -> Z
  down  down'
  -}
  𝕦 : {A : Set} → A → A
  𝕦 x = x

  comp : {A B C : Σ (Set × Set) (λ x → proj₁ x → proj₂ x)} → arr B C → arr A B → arr A C
  comp {(A0 , A1) , u} {(B0 , B1) , v} {(C0 , C1) , w} ((f0 , f1) , p) ((g0 , g1) , q) =
   ((λ x → f0 (g0 x)) , (λ z → f1 (g1 z))) , trans-comm-sq {A0} {B0} {C0} {A1} {B1} {C1} {g0} {g1} {f0} {f1} {u} {v} {w} q p
  idl : {A B : Σ (Set × Set) (λ x → proj₁ x → proj₂ x)} {f : arr A B} → comp {A} {B} {B} (((λ x → x) , (λ z → z)) , refl) f ≡ f
  idl {(A0 , A1) , u} {(B0 , B1) , v} {(f0 , f1) , p} = {!   !}
  idr : {A B : Σ (Set × Set) (λ x → proj₁ x → proj₂ x)} {f : arr A B} → comp {A} {A} {B} f (((λ x → x) , (λ z → z)) , refl) ≡ f
  idr {(A0 , A1) , u} {(B0 , B1) , v} {(f0 , f1) , p} = {!   !} -- trans-comm-sq {!   !} {!   !}

open Category arrow

-- just to see what happens:

arrow-cart : CartesianCategory (suc zero) zero zero
arrow-cart =
 record { U = arrow
        ; cartesian = record {
           terminal = record
            { ⊤ = (t , t) , (λ _ → ⊤)
            ; ⊤-is-terminal = record { ! = (λ _ → ⊤) , (λ _ → ⊤) ; !-unique = λ {A} → bang-uniq {A} }
            }
            ; products = record
             { product = λ {A} {B} → record
               { A×B = ((proj₁ (proj₁ A) × proj₁ (proj₁ B)) , (proj₂ (proj₁ A) × proj₂ (proj₁ B))) , λ x → (proj₂ A (proj₁ x)) , (proj₂ B) (proj₂ x)
               ; π₁ = proj₁ , proj₁
               ; π₂ = proj₂ , proj₂
               ; ⟨_,_⟩ = λ {C = C} f g → pair {C} {A} {B} f g
               ; project₁ = refl
               ; project₂ = refl
               ; unique = λ {refl refl → refl}
               } } } }
        where
        prod : Obj → Obj → Obj
        prod ((X , Y) , u) ((A , B) , v) = ((X × A) , (Y × B)) , λ x → (u (proj₁ x)) , (v (proj₂ x))
        bang-uniq : {A : Obj} (f : (arrow Category.⇒ A) ((t , t) , (λ _ → ⊤))) → ((λ _ → ⊤) , (λ _ → ⊤)) ≡ f
        bang-uniq (f0 , f1) =
         cong₂ _,_ (extensionality λ x → !-unique-lemma (f0 x)) (extensionality (λ x → !-unique-lemma (f1 x)))
        pair : {C A B : Obj} → (arrow Category.⇒ C) A → (arrow Category.⇒ C) B → (arrow Category.⇒ C) (prod A B)
        pair {(X , Y) , u} {(A , B) , v} {(E , F) , w} (f0 , f1) (g0 , g1) = (λ x → (f0 x) , (g0 x)) , (λ x → (f1 x) , (g1 x))


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
 ; curry = λ {C} {A} {B} g → cur {C} {A} {B} g
 ; eval-comp = refl
 ; curry-resp-≈ = λ {refl → refl}
 ; curry-unique = {!   !}
 }
 where
 prod : Obj → Obj → Obj
 prod ((X , Y) , u) ((A , B) , v) = ((X × A) , (Y × B)) , λ x → (u (proj₁ x)) , (v (proj₂ x))
 pair : {C A B : Obj} → (arrow Category.⇒ C) A → (arrow Category.⇒ C) B → (arrow Category.⇒ C) (prod A B)
 pair {(X , Y) , u} {(A , B) , v} {(E , F) , w} (f0 , f1) (g0 , g1) = (λ x → (f0 x) , (g0 x)) , (λ x → (f1 x) , (g1 x))
 bang-uniq : {A : Obj} (f : (arrow Category.⇒ A) ((t , t) , (λ _ → ⊤))) → ((λ _ → ⊤) , (λ _ → ⊤)) ≡ f
 bang-uniq (f0 , f1) = cong₂ _,_ (extensionality λ x → !-unique-lemma (f0 x)) (extensionality (λ x → !-unique-lemma (f1 x)))
 to-the : Obj → Obj → Obj
 to-the ((B0 , B1) , u) ((A0 , A1) , v) = (p , (A1 → B1)) , λ x a1 → proj₂ (proj₁ x) a1
  where
   p : Set
   p = Σ ((A0 → B0) × (A1 → B1)) λ r → (λ x → u ((proj₁ r) x)) ≡ (λ x → (proj₂ r) (v x))
 -- va implementato il pullback-hom di u e v : [v,u] fitta in
 {-
 [v,u]     → (A0 → B0)
   ↓ <- lei      ↓
 (A1 → B1) → (A0 → B1)
 -}
 ev : {B A : Obj} → (prod (to-the B A) A) ⇒ B
 ev {(B0 , B1) , u} {(A0 , A1)  , v} = dis , (λ z → proj₁ z (proj₂ z))
  where
   dis : proj₁ (proj₁ (prod (to-the ((B0 , B1) , u) ((A0 , A1) , v)) ((A0 , A1) , v))) → B0
   dis (((s , t) , p) , a0) = s a0
 cur : {C A B : Obj} → prod C A ⇒ B → C ⇒ to-the B A
 cur {(C0 , C1) , c} {(A0 , A1) , a} {(B0 , B1) , b} (fst , snd) =
  (λ x → ((λ y → fst (x , y)) , λ y → snd (c x , y)) , extensionality (λ y → {!   !})) , (λ z z₁ → snd (z , z₁))

-}