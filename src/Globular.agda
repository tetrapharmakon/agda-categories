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
The category of globular sets
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
  } where
      comp : {A B C : GlobObj} → GlobMor B C → GlobMor A B → GlobMor A C
      comp {globj A s t s-gi t-gi}
           {globj B s' t' s-gi' t-gi'}
           {globj C s'' t'' s-gi'' t-gi''}
           (glmor f eq-s eq-t)
           (glmor g eq-s' eq-t') = glmor (λ n → f n ∘ g n)
            (λ {n} →
              begin (f n ∘ g n) ∘ s n               ≈⟨ assoc ⟩
                    f n ∘ g n ∘ s n                 ≈⟨ refl⟩∘⟨ eq-s' ⟩
                    f n ∘ s' n ∘ g (1 + n)          ≈⟨ sym assoc ⟩
                    (f n ∘ s' n) ∘ g (1 + n)        ≈⟨ eq-s ⟩∘⟨refl ⟩
                    (s'' n ∘ f (1 + n)) ∘ g (1 + n) ≈⟨ assoc ⟩
                    s'' n ∘ f (1 + n) ∘ g (1 + n)   ∎)
            (λ {n} →
              begin (f n ∘ g n) ∘ t n               ≈⟨ assoc ⟩
                    f n ∘ g n ∘ t n                 ≈⟨ refl⟩∘⟨ eq-t' ⟩
                    f n ∘ t' n ∘ g (1 + n)          ≈⟨ sym assoc ⟩
                    (f n ∘ t' n) ∘ g (1 + n)        ≈⟨ eq-t ⟩∘⟨refl ⟩
                    (t'' n ∘ f (1 + n)) ∘ g (1 + n) ≈⟨ assoc ⟩
                    t'' n ∘ f (1 + n) ∘ g (1 + n)   ∎)

Γ : {ac : AllCoproductsOf Level.zero} → Functor Globs aNets
Γ {ac} = record
  { F₀ = Γ0
  ; F₁ = Γ1
  ; identity = λ { {globj E s t gi-s gi-t} → let
      open IndexedCoproductOf (ac E) in
      unique′ _ _
        (λ i → begin ⟨ (λ i₁ → ι i₁ ∘ id) ⟩ ∘ ι i ≈⟨ commute _ i ⟩
                    ι i ∘ id                      ≈⟨ id-comm ⟩
                     id ∘ ι i                     ∎)}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → Γhom {X} {Y} {Z} {f} {g}
  ; F-resp-≈ = λ { {X} {Y} {f} {g} x → Γresp {X} {Y} {f} {g} x}
  } where
      σ : (O : GlobObj) → (i : ℕ) → (GlobObj.E O) i ⇒ _
      σ (globj E s t gi-s gi-t) zero = ι 0
        where open IndexedCoproductOf (ac E)
      σ (globj E s t gi-s gi-t) (suc i) = ι i ∘ s i
        where open IndexedCoproductOf (ac E)

      Γhom : {X Y Z : GlobObj} {f : GlobMor X Y} {g : GlobMor Y Z} → _
      Γhom {globj A sA tA gi-sA gi-tA}
           {globj B sB tB gi-sB gi-tB}
           {globj C sC tC gi-sC gi-tC}
           {glmor f eq-s eq-t}
           {glmor g eq-s' eq-t'} =
              begin A.⟨ (λ i → C.ι i ∘ g i ∘ f i) ⟩ ≈⟨ A.⟨⟩-cong _ _ (λ i → sym-assoc) ⟩
                   A.⟨ (λ i → (C.ι i ∘ g i) ∘ f i) ⟩ ≈⟨ A.⟨⟩-cong _ _ (λ i → pushˡ (sym (B.commute _ _))) ⟩
                   A.⟨ (λ i → B.⟨ (λ j → C.ι j ∘ g j) ⟩ ∘ B.ι i ∘ f i) ⟩ ≈⟨ sym (A.⟨⟩∘ _ _) ⟩
                   B.⟨ (λ i → C.ι i ∘ g i) ⟩ ∘ A.⟨ (λ i → B.ι i ∘ f i) ⟩ ∎
              where module A = IndexedCoproductOf (ac A)
                    module B = IndexedCoproductOf (ac B)
                    module C = IndexedCoproductOf (ac C)
      Γresp : {X Y : GlobObj} {f g : GlobMor X Y} (f=g : ∀ {i : ℕ} → GlobMor.f f i ≈ GlobMor.f g i) → _
      Γresp {globj A s t gi-s gi-t}
            {globj B sB tB gi-sB gi-tB}
            {glmor f eq-sf eq-tf}
            {glmor g eq-sg eq-tg} f≈g = A.⟨⟩-cong {B.X} (λ i → B.ι i ∘ f i) (λ i → B.ι i ∘ g i) λ i → refl⟩∘⟨ f≈g
              where module A = IndexedCoproductOf (ac A)
                    module B = IndexedCoproductOf (ac B)
      τ : (O : GlobObj) → (i : ℕ) → (GlobObj.E O) i ⇒ _
      τ (globj E s t gi-s gi-t) zero = ι 0
        where open IndexedCoproductOf (ac E)
      τ (globj E s t gi-s gi-t) (suc i) = ι i ∘ t i
        where open IndexedCoproductOf (ac E)

      Γ0 : ∀ (G : GlobObj) → ANetObj
      Γ0 G@(globj E s t gi-s gi-t) = anetobj {X} ⟨ σ G ⟩ ⟨ τ G ⟩
        where open IndexedCoproductOf (ac E)

      Γ1 : ∀ {A B} → GlobMor A B → _
      Γ1 A@{globj E s t gi-s gi-t}
         B@{globj F s₁ t₁ gi-s₁ gi-t₁}
         (glmor f eq-s eq-t) =
           anetmor A.⟨ help ⟩
           (begin A.⟨ (λ i → B.ι i ∘ f i) ⟩ ∘ A.⟨ σ A ⟩              ≈⟨ A.⟨⟩∘ _ _ ⟩
                  A.⟨ (λ i → A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ σ A i) ⟩ ≈⟨ A.⟨⟩-cong _ _ prop ⟩
                  A.⟨ (λ i → B.⟨ σ B ⟩ ∘ B.ι i ∘ f i) ⟩              ≈⟨ sym (A.⟨⟩∘ _ _) ⟩
                  B.⟨ σ B ⟩ ∘ A.⟨ (λ i → B.ι i ∘ f i) ⟩              ∎)
           (begin A.⟨ (λ i → B.ι i ∘ f i) ⟩ ∘ A.⟨ τ A ⟩              ≈⟨ A.⟨⟩∘ _ _ ⟩
                  A.⟨ (λ i → A.⟨ (λ i₁ → B.ι i₁ ∘ f i₁) ⟩ ∘ τ A i) ⟩ ≈⟨ A.⟨⟩-cong _ _ prop2 ⟩
                  A.⟨ (λ i → B.⟨ τ B ⟩ ∘ B.ι i ∘ f i) ⟩              ≈⟨ sym (A.⟨⟩∘ _ _) ⟩
                  B.⟨ τ B ⟩ ∘ A.⟨ (λ i → B.ι i ∘ f i) ⟩              ∎)
        where module A = IndexedCoproductOf (ac E)
              module B = IndexedCoproductOf (ac F)
              help : (i : ℕ) → E i ⇒ B.X
              help i = B.ι i ∘ f i

              prop : (i : ℕ) → A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ σ A i ≈ B.⟨ σ B ⟩ ∘ B.ι i ∘ f i
              prop ℕ.zero =
                begin A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ A.ι 0 ≈⟨ A.commute _ ℕ.zero ⟩
                      B.ι 0 ∘ f 0                          ≈⟨ sym (B.commute (σ B) 0) ⟩∘⟨refl ⟩
                      (B.⟨ σ B ⟩ ∘ B.ι 0) ∘ f 0            ≈⟨ assoc ⟩
                      B.⟨ σ B ⟩ ∘ B.ι 0 ∘ f 0              ∎
              prop (ℕ.suc i) =
                begin A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ A.ι i ∘ s i    ≈⟨ sym-assoc ⟩
                      (A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ A.ι i) ∘ s i  ≈⟨ A.commute _ i ⟩∘⟨refl ⟩
                      (B.ι i ∘ f i) ∘ s i                           ≈⟨ assoc ⟩
                      B.ι i ∘ f i ∘ s i                             ≈⟨ refl⟩∘⟨ eq-s ⟩
                      B.ι i ∘ s₁ i ∘ f (ℕ.suc i)                    ≈⟨ sym-assoc ⟩
                      (B.ι i ∘ s₁ i) ∘ f (ℕ.suc i)                  ≈⟨ sym (B.commute (σ B) (1 + i)) ⟩∘⟨refl ⟩
                      (B.⟨ σ B ⟩ ∘ B.ι (ℕ.suc i)) ∘ f (ℕ.suc i)     ≈⟨ assoc ⟩
                      B.⟨ σ B ⟩ ∘ B.ι (ℕ.suc i) ∘ f (ℕ.suc i)       ∎
              -- same as prop, but for t
              prop2 : (i : ℕ) → A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ τ A i ≈ B.⟨ τ B ⟩ ∘ B.ι i ∘ f i
              prop2 ℕ.zero =
                begin A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ A.ι 0  ≈⟨ A.commute (λ j → B.ι j ∘ f j) ℕ.zero ⟩
                      B.ι 0 ∘ f 0                           ≈⟨ sym (B.commute (τ B) 0) ⟩∘⟨refl ⟩
                      (B.⟨ τ B ⟩ ∘ B.ι 0) ∘ f 0             ≈⟨ assoc ⟩
                      B.⟨ τ B ⟩ ∘ B.ι 0 ∘ f 0               ∎
              prop2 (ℕ.suc i) =
                begin A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ A.ι i ∘ t i    ≈⟨ sym-assoc ⟩
                      (A.⟨ (λ j → B.ι j ∘ f j) ⟩ ∘ A.ι i) ∘ t i  ≈⟨ A.commute _ i ⟩∘⟨refl ⟩
                      (B.ι i ∘ f i) ∘ t i                           ≈⟨ assoc ⟩
                      B.ι i ∘ f i ∘ t i                             ≈⟨ refl⟩∘⟨ eq-t ⟩
                      B.ι i ∘ t₁ i ∘ f (ℕ.suc i)                    ≈⟨ sym-assoc ⟩
                      (B.ι i ∘ t₁ i) ∘ f (ℕ.suc i)                  ≈⟨ sym (B.commute (τ B) (1 + i)) ⟩∘⟨refl ⟩
                      (B.⟨ τ B ⟩ ∘ B.ι (ℕ.suc i)) ∘ f (ℕ.suc i)     ≈⟨ assoc ⟩
                      B.⟨ τ B ⟩ ∘ B.ι (ℕ.suc i) ∘ f (ℕ.suc i)       ∎