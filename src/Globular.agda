{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Data.Product

module Globular {o ℓ e} (ℂ : Category o ℓ e) where

open Category ℂ
open HomReasoning
open Equiv

open import Level
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Categories.Adjoint
open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian as c
open import Categories.Category.Cocartesian as cc
open import Categories.Category.Cocomplete.Finitely ℂ
open import Categories.Category.Cocomplete
open import Categories.Category.Complete.Finitely ℂ
open import Categories.Diagram.Coequalizer ℂ
open import Categories.Category.Lift
open import Categories.Diagram.Equalizer ℂ
open import Categories.Diagram.Pullback ℂ
open import Categories.Functor.Core
open import Categories.Morphism.Reasoning ℂ
open import Categories.Object.Coproduct
open import ArrowNet ℂ

open import Categories.Object.Coproduct.Indexed ℂ
open import Categories.Object.Coproduct.Indexed.Properties ℂ


{-
CATEGORIES
===
arrow network; an arrow network is a set equipped with an action
of the free monoid on two generators, called s,t to make evident
that an arrow network is also a special kind of graph (where the
object of vertices and of edges coincide).
-}
record GlobObj : Set (o ⊔ ℓ ⊔ e) where
  constructor globj
  field
    E : ℕ → Obj
    s t : ∀ (n : ℕ) → E (1 + n) ⇒ E n
    --
    gi-s : ∀ {n : ℕ} → s n ∘ s (1 + n) ≈ s n ∘ t (1 + n)
    gi-t : ∀ {n : ℕ} → t n ∘ s (1 + n) ≈ t n ∘ t (1 + n)


record GlobMor (G H : GlobObj) : Set (o ⊔ ℓ ⊔ e) where
  constructor glmor
  private
    module G = GlobObj G
    module H = GlobObj H
  field
    f : ∀ (n : ℕ) → G.E n ⇒ H.E n
    eq-s : ∀ {n : ℕ} → f n ∘ G.s n ≈ H.s n ∘ f (1 + n)
    eq-t : ∀ {n : ℕ} → f n ∘ G.t n ≈ H.t n ∘ f (1 + n)

Globs : Category _ _ _
Globs = record
  { Obj = GlobObj
  ; _⇒_ = λ G H → GlobMor G H
  ; _≈_ = λ {(glmor f eq-s eq-t) (glmor g eq-s' eq-t') → ∀ {n : ℕ} → f n ≈ g n}
  ; id = glmor (λ _ → id) id-comm-sym id-comm-sym
  ; _∘_ = comp
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = λ x → sym x
    ; trans = λ p q → trans p q
    }
  ; ∘-resp-≈ = λ p q → ∘-resp-≈ p q
  } where comp : {A B C : GlobObj} → GlobMor B C → GlobMor A B → GlobMor A C
          comp {globj A s t s-gi t-gi} {globj B s' t' s-gi' t-gi'} {globj C s'' t'' s-gi'' t-gi''} (glmor f eq-s eq-t) (glmor g eq-s' eq-t') = glmor (λ n → f n ∘ g n)
            (λ {n} → begin (f n ∘ g n) ∘ s n ≈⟨ assoc ⟩
                           f n ∘ g n ∘ s n ≈⟨ refl⟩∘⟨ eq-s' ⟩
                           f n ∘ s' n ∘ g (1 + n) ≈⟨ sym assoc ⟩
                           (f n ∘ s' n) ∘ g (1 + n) ≈⟨ eq-s ⟩∘⟨refl ⟩
                           (s'' n ∘ f (1 + n)) ∘ g (1 + n) ≈⟨ assoc ⟩
                           s'' n ∘ f (1 + n) ∘ g (1 + n) ∎)
            (λ {n} → begin (f n ∘ g n) ∘ t n ≈⟨ assoc ⟩
                           f n ∘ g n ∘ t n ≈⟨ refl⟩∘⟨ eq-t' ⟩
                           f n ∘ t' n ∘ g (1 + n) ≈⟨ sym assoc ⟩
                           (f n ∘ t' n) ∘ g (1 + n) ≈⟨ eq-t ⟩∘⟨refl ⟩
                           (t'' n ∘ f (1 + n)) ∘ g (1 + n) ≈⟨ assoc ⟩
                           t'' n ∘ f (1 + n) ∘ g (1 + n) ∎)



Γ : {ac : AllCoproductsOf Level.zero} → Functor Globs aNets
Γ {ac} = record
  { F₀ = gioco
  ; F₁ = giocoM
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  } where
      sigma : (O : GlobObj) → (i : ℕ) → (GlobObj.E O) i ⇒ _
      sigma (globj E s t gi-s gi-t) zero = ι 0
        where open IndexedCoproductOf (ac E)
      sigma (globj E s t gi-s gi-t) (suc i) = ι i ∘ s i
        where open IndexedCoproductOf (ac E)


      tau : (O : GlobObj) → (i : ℕ) → (GlobObj.E O) i ⇒ _
      tau (globj E s t gi-s gi-t) zero = ι 0
        where open IndexedCoproductOf (ac E)
      tau (globj E s t gi-s gi-t) (suc i) = ι i ∘ t i
        where open IndexedCoproductOf (ac E)

      gioco : ∀ (G : GlobObj) → ANetObj
      gioco O@(globj E s t gi-s gi-t) = anetobj {X} ⟨ sigma O ⟩ ⟨ tau O ⟩
        where open IndexedCoproductOf (ac E)


      giocoM : ∀ {A B} → GlobMor A B → _
      giocoM A@{globj E s t gi-s gi-t} B@{globj E₁ s₁ t₁ gi-s₁ gi-t₁} (glmor f eq-s eq-t) = anetmor A.⟨ pollo ⟩
                      (begin A.⟨ (λ i → B.ι i ∘ f i) ⟩ ∘ A.⟨ sigma A ⟩              ≈⟨ A.⟨⟩∘ _ _ ⟩
                             A.⟨ (λ i → A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ sigma A i) ⟩ ≈⟨ A.⟨⟩-cong _ _ prop ⟩
                             A.⟨ (λ i → B.⟨ sigma B ⟩ ∘ B.ι i ∘ f i) ⟩              ≈⟨ sym (A.⟨⟩∘ _ _) ⟩
                             B.⟨ sigma B ⟩ ∘ A.⟨ (λ i → B.ι i ∘ f i) ⟩              ∎)
                      (begin A.⟨ (λ i → B.ι i ∘ f i) ⟩ ∘ A.⟨ tau A ⟩              ≈⟨ A.⟨⟩∘ _ _ ⟩
                             A.⟨ (λ i → A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ tau A i) ⟩ ≈⟨ A.⟨⟩-cong _ _ prop2 ⟩
                             A.⟨ (λ i → B.⟨ tau B ⟩ ∘ B.ι i ∘ f i) ⟩              ≈⟨ sym (A.⟨⟩∘ _ _) ⟩
                             B.⟨ tau B ⟩ ∘ A.⟨ (λ i → B.ι i ∘ f i) ⟩              ∎)
        where module A = IndexedCoproductOf (ac E)
              module B = IndexedCoproductOf (ac E₁)
              pollo : (i : ℕ) → E i ⇒ B.X
              pollo i = B.ι i ∘ f i

              prop : (i : ℕ) → A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ sigma A i
                             ≈ B.⟨ sigma B ⟩ ∘ B.ι i ∘ f i
              prop ℕ.zero = begin A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ A.ι 0 ≈⟨ A.commute (λ i₁ → B.ι i₁ ∘ f i₁) ℕ.zero ⟩
                                  B.ι 0 ∘ f 0                          ≈⟨ sym (B.commute (sigma B) 0) ⟩∘⟨refl ⟩
                                  (B.⟨ sigma B ⟩ ∘ B.ι 0) ∘ f 0        ≈⟨ assoc ⟩
                                  B.⟨ sigma B ⟩ ∘ B.ι 0 ∘ f 0          ∎
              prop (ℕ.suc i) = begin A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ A.ι i ∘ s i    ≈⟨ sym-assoc ⟩
                                     (A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ A.ι i) ∘ s i  ≈⟨ A.commute (λ i₁ → B.ι i₁ ∘ f i₁) i ⟩∘⟨refl ⟩
                                     (B.ι i ∘ f i) ∘ s i                           ≈⟨ assoc ⟩
                                     B.ι i ∘ f i ∘ s i                             ≈⟨ refl⟩∘⟨ eq-s ⟩
                                     B.ι i ∘ s₁ i ∘ f (ℕ.suc i)                    ≈⟨ sym-assoc ⟩
                                     (B.ι i ∘ s₁ i) ∘ f (ℕ.suc i)                  ≈⟨ sym (B.commute (sigma B) (1 + i)) ⟩∘⟨refl ⟩
                                     (B.⟨ sigma B ⟩ ∘ B.ι (ℕ.suc i)) ∘ f (ℕ.suc i) ≈⟨ assoc ⟩
                                     B.⟨ sigma B ⟩ ∘ B.ι (ℕ.suc i) ∘ f (ℕ.suc i)   ∎

              prop2 : (i : ℕ) → A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ tau A i
                             ≈ B.⟨ tau B ⟩ ∘ B.ι i ∘ f i
              prop2 ℕ.zero = begin A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ A.ι 0 ≈⟨ A.commute (λ i₁ → B.ι i₁ ∘ f i₁) ℕ.zero ⟩
                                  B.ι 0 ∘ f 0                        ≈⟨ sym (B.commute (tau B) 0) ⟩∘⟨refl ⟩
                                  (B.⟨ tau B ⟩ ∘ B.ι 0) ∘ f 0        ≈⟨ assoc ⟩
                                  B.⟨ tau B ⟩ ∘ B.ι 0 ∘ f 0          ∎
              prop2 (ℕ.suc i) = begin A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ A.ι i ∘ t i   ≈⟨ sym-assoc ⟩
                                     (A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ A.ι i) ∘ t i  ≈⟨ A.commute (λ i₁ → B.ι i₁ ∘ f i₁) i ⟩∘⟨refl ⟩
                                     (B.ι i ∘ f i) ∘ t i                           ≈⟨ assoc ⟩
                                     B.ι i ∘ f i ∘ t i                             ≈⟨ refl⟩∘⟨ eq-t ⟩
                                     B.ι i ∘ t₁ i ∘ f (ℕ.suc i)                    ≈⟨ sym-assoc ⟩
                                     (B.ι i ∘ t₁ i) ∘ f (ℕ.suc i)                  ≈⟨ sym (B.commute (tau B) (1 + i)) ⟩∘⟨refl ⟩
                                     (B.⟨ tau B ⟩ ∘ B.ι (ℕ.suc i)) ∘ f (ℕ.suc i)   ≈⟨ assoc ⟩
                                     B.⟨ tau B ⟩ ∘ B.ι (ℕ.suc i) ∘ f (ℕ.suc i)     ∎

        --where pollo :



      --anetmor {! ⟨ pollo ⟩  !} {!   !} {!   !}
        --where pollo :


{-

λ { (globj E s t gi-s gi-t) →
              let open IndexedCoproductOf (ac E)
                  pippo : (i : ℕ) → E i ⇒ X
                  pippo i = {! i !}
                  sigma : X ⇒ X
                  sigma = ⟨ pippo ⟩
                  tau : X ⇒ X
                  tau = {!   !}
               in anetobj {X} sigma tau }

               -}
