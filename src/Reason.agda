{-# OPTIONS --safe --without-K #-}

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Function using (flip)

-- A custom module to *quickly* reason about morphisms in a category in the agda-categories library

module Reason {o ℓ e} (C : Category o ℓ e) where

open Category C public

open Equiv public

open module Chain = HomReasoning

assoc-2 = assoc

sym-assoc-2 = sym-assoc

infixr 7 _∙_
_∙_ = Equiv.trans

assoc-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} → (f ∘ g ∘ h) ∘ i ≈ f ∘ g ∘ h ∘ i
assoc-3 = assoc ∙ ∘-resp-≈ʳ assoc

assoc-4 : ∀ {A B C D E F} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {j : F ⇒ E} → (f ∘ g ∘ h ∘ i) ∘ j ≈ f ∘ g ∘ h ∘ i ∘ j
assoc-4 = assoc ∙ ∘-resp-≈ʳ assoc-3

assoc-5 : ∀ {A B C D E F G} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {j : F ⇒ E} {k : G ⇒ F} → (f ∘ g ∘ h ∘ i ∘ j) ∘ k ≈ f ∘ g ∘ h ∘ i ∘ j ∘ k
assoc-5 = assoc ∙ ∘-resp-≈ʳ assoc-4

assoc-6 : ∀ {A B C D E F G H} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {j : F ⇒ E} {k : G ⇒ F} {l : H ⇒ G} → (f ∘ g ∘ h ∘ i ∘ j ∘ k) ∘ l ≈ f ∘ g ∘ h ∘ i ∘ j ∘ k ∘ l
assoc-6 = assoc ∙ ∘-resp-≈ʳ assoc-5

sym-assoc-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} → f ∘ g ∘ h ∘ i ≈ (f ∘ g ∘ h) ∘ i
sym-assoc-3 = Equiv.sym assoc-3

sym-assoc-4 : ∀ {A B C D E F} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {j : F ⇒ E} → f ∘ g ∘ h ∘ i ∘ j ≈ (f ∘ g ∘ h ∘ i) ∘ j
sym-assoc-4 = Equiv.sym assoc-4

anti-assoc-4 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} → ((f ∘ g) ∘ h) ∘ i ≈ f ∘ g ∘ h ∘ i
anti-assoc-4 = assoc ∙ assoc

anti-assoc-5 : ∀ {A B C D E F} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {j : F ⇒ E} → (((f ∘ g) ∘ h) ∘ i) ∘ j ≈ f ∘ g ∘ h ∘ i ∘ j
anti-assoc-5 = assoc ∙ anti-assoc-4

skip-1 : ∀ {A B C} {f : B ⇒ A} {z z′ : C ⇒ B} → z ≈ z′ → f ∘ z ≈ f ∘ z′
skip-1 = ∘-resp-≈ʳ

skip = skip-1

skip-2 : ∀ {A B C D} {f : B ⇒ A} {g : C ⇒ B} {z z′ : D ⇒ C} → z ≈ z′ → f ∘ g ∘ z ≈ f ∘ g ∘ z′
skip-2 eq = skip-1 (skip-1 eq)

skip-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {z z′ : E ⇒ D} → z ≈ z′ → f ∘ g ∘ h ∘ z ≈ f ∘ g ∘ h ∘ z′
skip-3 eq = skip-1 (skip-2 eq)

skip-4 : ∀ {A B C D E F} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {z z′ : F ⇒ E} → z ≈ z′ → f ∘ g ∘ h ∘ i ∘ z ≈ f ∘ g ∘ h ∘ i ∘ z′
skip-4 eq = skip-1 (skip-3 eq)

skip-5 : ∀ {A B C D E F G} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {j : F ⇒ E} {z z′ : G ⇒ F} → z ≈ z′ → f ∘ g ∘ h ∘ i ∘ j ∘ z ≈ f ∘ g ∘ h ∘ i ∘ j ∘ z′
skip-5 eq = skip-1 (skip-4 eq)

rw : ∀ {A B C} {f f′ : B ⇒ A} {g : C ⇒ B} → f ≈ f′ → f ∘ g ≈ f′ ∘ g
rw = ∘-resp-≈ˡ

rw-1-2 : ∀ {A B C D} {f : B ⇒ A} {g : C ⇒ B} {fg : C ⇒ A} {z : D ⇒ C} → fg ≈ f ∘ g  → fg ∘ z ≈ f ∘ g ∘ z
rw-1-2 eq = rw eq ∙ assoc

rw-2-1 : ∀ {A B C D} {f : B ⇒ A} {g : C ⇒ B} {fg : C ⇒ A} {z : D ⇒ C} → f ∘ g ≈ fg → f ∘ g ∘ z ≈ fg ∘ z
rw-2-1 eq = sym-assoc ∙ rw eq

rw-3-1 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {fgh : D ⇒ A} {z : E ⇒ D} → f ∘ g ∘ h ≈ fgh → f ∘ g ∘ h ∘ z ≈ fgh ∘ z
rw-3-1 eq = sym-assoc-3 ∙ rw eq

rw-1-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {fgh : D ⇒ A} {z : E ⇒ D} → fgh ≈ f ∘ g ∘ h  → fgh ∘ z ≈ f ∘ g ∘ h ∘ z
rw-1-3 eq = sym (rw-3-1 (sym eq))

rw-2 : ∀ {A B B′ C D} {f : B ⇒ A} {g : C ⇒ B} {f′ : B′ ⇒ A} {g′ : C ⇒ B′} {z : D ⇒ C} → f ∘ g ≈ f′ ∘ g′ → f ∘ g ∘ z ≈ f′ ∘ g′ ∘ z
rw-2 eq = sym-assoc-2 ∙ rw eq ∙ assoc-2

-- A B C     A B′ B C
rw-2-3 : ∀ {A B C B′ C′ Z} {f : A ⇒ B} {g : B ⇒ C}
                            {h : A ⇒ B′} {i : B′ ⇒ C′} {j : C′ ⇒ C}
                            {z : Z ⇒ A}
        → g ∘ f ≈ j ∘ i ∘ h
        → g ∘ f ∘ z ≈ j ∘ i ∘ h ∘ z
rw-2-3 eq = sym-assoc-2 ∙ rw eq ∙ assoc-3

-- A B C     A B′ B C
rw-3-3 : ∀ {A B C D B′ C′ Z} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} {i : C′ ⇒ D} {j : B′ ⇒ C′} {k : A ⇒ B′}  {z : Z ⇒ A}
        → f ∘ g ∘ h ≈ i ∘ j ∘ k
        → f ∘ g ∘ h ∘ z ≈ i ∘ j ∘ k ∘ z
rw-3-3 eq = sym-assoc-3 ∙ rw eq ∙ assoc-3

id-0 = identityˡ

sym-id-0 : ∀ {A B} {f : A ⇒ B} → f ≈ id ∘ f
sym-id-0 = Equiv.sym identityˡ

id-1 = identityʳ

sym-id-1 : ∀ {A B} {f : A ⇒ B} → f ≈ f ∘ id
sym-id-1 = Equiv.sym id-1

id-2 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ g ∘ id ≈ f ∘ g
id-2 = skip identityʳ

id-3 : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} → f ∘ g ∘ h ∘ id ≈ f ∘ g ∘ h
id-3 = skip-2 identityʳ

id-4 : ∀ {A B C D E} {f : D ⇒ E} {g : C ⇒ D} {h : B ⇒ C} {i : A ⇒ B} → f ∘ g ∘ h ∘ i ∘ id ≈ f ∘ g ∘ h ∘ i
id-4 = skip-3 identityʳ

id-5 : ∀ {A B C D E F} {f : E ⇒ F} {g : D ⇒ E} {h : C ⇒ D} {i : B ⇒ C} {j : A ⇒ B} → f ∘ g ∘ h ∘ i ∘ j ∘ id ≈ f ∘ g ∘ h ∘ i ∘ j
id-5 = skip-4 identityʳ

id-6 : ∀ {A B C D E F G} {f : F ⇒ G} {g : E ⇒ F} {h : D ⇒ E} {i : C ⇒ D} {j : B ⇒ C} {k : A ⇒ B} → f ∘ g ∘ h ∘ i ∘ j ∘ k ∘ id ≈ f ∘ g ∘ h ∘ i ∘ j ∘ k
id-6 = skip-5 identityʳ

sym-id-2 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ g ≈ f ∘ g ∘ id
sym-id-2 = Equiv.sym id-2

idm-1 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ id ∘ g ≈ f ∘ g
idm-1 = skip identityˡ

idm-2 : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} → f ∘ g ∘ id ∘ h ≈ f ∘ g ∘ h
idm-2 = skip-2 identityˡ

sym-idm-1 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ g ≈ f ∘ id ∘ g
sym-idm-1 = Equiv.sym idm-1

id-2-1 : ∀ {A B} {f : A ⇒ B} → f ∘ id ∘ id ≈ f
id-2-1 = id-2 ∙ id-1

id-swap : ∀ {A B} {f : B ⇒ A} → f ∘ id ≈ id ∘ f
id-swap = identityʳ ∙ Equiv.sym identityˡ

id-swap-2 : ∀ {A B} {f : B ⇒ A} → f ∘ id ∘ id ≈ id ∘ id ∘ f
id-swap-2 = rw-2 id-swap ∙ skip id-swap

sym-id-swap : ∀ {A B} {f : B ⇒ A} → id ∘ f ≈ f ∘ id
sym-id-swap = identityˡ ∙ Equiv.sym identityʳ

sym-id-swap-2 : ∀ {A B} {f : B ⇒ A} → id ∘ id ∘ f ≈ f ∘ id ∘ id
sym-id-swap-2 = Equiv.sym id-swap-2

cancel : ∀ {A B} {f : A ⇒ A} {g : B ⇒ A}
         → f ≈ id
         → f ∘ g ≈ g
cancel eq = rw eq ∙ identityˡ

cancel-1 : ∀ {A B} {f : A ⇒ B} {g : A ⇒ A}
         → g ≈ id
         → f ∘ g ≈ f
cancel-1 eq = skip eq ∙ identityʳ

cancel-2 : ∀ {A B Z} {f : B ⇒ A} {g : A ⇒ B} {z : Z ⇒ A}
         → f ∘ g ≈ id
         → f ∘ g ∘ z ≈ z
cancel-2 eq = rw-2-1 eq ∙ identityˡ

cancel-3 : ∀ {A B C Z} {f : B ⇒ A} {g : C ⇒ B} {h : A ⇒ C} {z : Z ⇒ A}
         → f ∘ g ∘ h ≈ id
         → f ∘ g ∘ h ∘ z ≈ z
cancel-3 eq = rw-3-1 eq ∙ identityˡ

cancel-end-2 : ∀ {A B C} {f : A ⇒ A} {a : B ⇒ C} {b : A ⇒ B}
         → f ≈ id
         → a ∘ b ∘ f ≈ a ∘ b
cancel-end-2 eq = skip (cancel-1 eq)

cancel-end-3 : ∀ {A B C D} {f : A ⇒ A} {a : C ⇒ D} {b : B ⇒ C} {c : A ⇒ B}
         → f ≈ id
         → a ∘ b ∘ c ∘ f ≈ a ∘ b ∘ c
cancel-end-3 eq = skip-2 (cancel-1 eq)

id2 : ∀ {A B} {f : A ⇒ B} → id ∘ id ∘ f ≈ f
id2 = id-0 ∙ id-0

intro-0 : ∀ {A B} {f : A ⇒ A} {g : B ⇒ A}
         → f ≈ id
         → g ≈ f ∘ g
intro-0 eq = sym (rw eq ∙ identityˡ)

intro-1 : ∀ {A B} {f : B ⇒ B} {g : B ⇒ A}
         → f ≈ id
         → g ≈ g ∘ f
intro-1 eq = sym (skip eq ∙ identityʳ)

intro-2 : ∀ {A B Z} {f : B ⇒ A} {g : A ⇒ B} {z : Z ⇒ A}
         → f ∘ g ≈ id
         → z ≈ f ∘ g ∘ z
intro-2 eq = sym (cancel-2 eq)
