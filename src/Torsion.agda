{-# OPTIONS --safe --without-K #-}

open import Categories.Category using (Category)
module Torsion {o ℓ e} {C : Category o ℓ e} where

open import Data.Product using (_,_; _×_)

open import Categories.Category.SubCategory C
open import Categories.Functor.Construction.SubCategory using (FullSub)

open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Adjoint using (_⊣_) renaming (Adjoint to Adj)
open import Categories.Object.Initial using (Initial)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Zero C using (Zero)
open import Categories.Functor.Construction.Constant using (const; constˡ)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ᵥ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_)
open import Categories.Category.Product using (Product; _※_; πʳ)
open import Categories.Category.Equivalence using (StrongEquivalence; WeakInverse)
open import Categories.Adjoint.Monadic using (IsMonadicAdjunction)
open import Categories.Adjoint.Compose using (_∘⊣_)

open Category C
open HomReasoning
open Equiv

open import Level

-- a cleft on C: a pair of full subcategories (𝓣, 𝓕) such that
-- the inclusion 𝓣 ↪️ C has a right adjoint and the inclusion 𝓕 ↪️ C has a left adjoint .

record Cleft {a b : Level} (I : Set a) (J : Set b) : Set (o ⊔ ℓ ⊔ e ⊔ a ⊔ b) where
  field
    𝓣   : I → Obj
    𝓕   : J → Obj
    iR  : Functor C (FullSubCategory 𝓣)
  
  i = FullSub C {U = 𝓣}
  qR = FullSub C {U = 𝓕}
  
  field
    𝓣⊣  : i ⊣ iR
    q   : Functor C (FullSubCategory 𝓕)
    𝓕⊣  : q ⊣ qR

  -- Combined reflection/coreflection into the product category.
  K : Functor C (Product (FullSubCategory 𝓣) (FullSubCategory 𝓕))
  K = iR ※ q

  -- Explicit pieces of the essential sequence.
  i∘iR : Functor C C
  i∘iR = i ∘F iR

  qR∘q : Functor C C
  qR∘q = qR ∘F q

  -- Counit of i ⊣ iR, viewed as i∘iR ⇒ id.
  counitᵢ : NaturalTransformation i∘iR idF
  counitᵢ = Adj.counit 𝓣⊣

  -- Unit of q ⊣ qR, viewed as id ⇒ qR∘q.
  unit_q : NaturalTransformation idF qR∘q
  unit_q = Adj.unit 𝓕⊣

  -- The composed arrow i iR X → X → qR q X, natural in X.
  essential : NaturalTransformation i∘iR qR∘q
  essential = unit_q ∘ᵥ counitᵢ

  -- The "essential sequence" of a cleft: from the counit of the adjunction i ⊣ iR and the unit of the adjunction q ⊣ qR, we get two composable arrows in C:
  -- i iR x → x → qR q x for each object x of C.
  -- When C has an initial and a terminal object, one can consider the sequence
  -- Ø → i iR x → x → qR q x → 1

-- Refinements/variations of a cleft.

record SplitCleft {a b : Level} (I : Set a) (J : Set b) : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)) where
  field
    cleft : Cleft I J

  private
    FS𝓣 = FullSubCategory (Cleft.𝓣 cleft)
    FS𝓕 = FullSubCategory (Cleft.𝓕 cleft)
    P   = Product FS𝓣 FS𝓕
    K   = Cleft.K cleft

  field
    qL   : Functor FS𝓕 C
    -- Note: this is definitionally the same as adjointness to `Cleft.q cleft` on
    -- object/morphism parts, but avoids proof-field definitional equalities.
    qL⊣q : qL ⊣ (πʳ {C = FS𝓣} {D = FS𝓕} ∘F K)


record SDirCleft {a b : Level} (I : Set a) (J : Set b) : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)) where
  field
    cleft : Cleft I J

  private
    FS𝓣 = FullSubCategory (Cleft.𝓣 cleft)
    FS𝓕 = FullSubCategory (Cleft.𝓕 cleft)
    P   = Product FS𝓣 FS𝓕
    K   = Cleft.K cleft

  field
    KL        : Functor P C
    KL⊣K      : KL ⊣ K
    K-monadic : IsMonadicAdjunction KL⊣K


FoA : ∀ {a b : Level} (I : Set a) (J : Set b) → Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b))
FoA I J = SDirCleft I J


record RectangularCleft {a b : Level} (I : Set a) (J : Set b) : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)) where
  field
    cleft : Cleft I J

  private
    FS𝓣 = FullSubCategory (Cleft.𝓣 cleft)
    FS𝓕 = FullSubCategory (Cleft.𝓕 cleft)
    P   = Product FS𝓣 FS𝓕
    K   = Cleft.K cleft

  field
    K⁻¹         : Functor P C
    K∘K⁻¹≈id    : NaturalIsomorphism (K ∘F K⁻¹) (idF {C = P})
    K⁻¹∘K≈id    : NaturalIsomorphism (K⁻¹ ∘F K) (idF {C = C})

  K-weakInverse : WeakInverse K K⁻¹
  K-weakInverse = record
    { F∘G≈id = K∘K⁻¹≈id
    ; G∘F≈id = K⁻¹∘K≈id
    }

  K-equivalence : StrongEquivalence C P
  K-equivalence = record
    { F = K
    ; G = K⁻¹
    ; weak-inverse = K-weakInverse
    }


record TorsionTheory {a b : Level} (I : Set a) (J : Set b) : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)) where
  field
    cleft : Cleft I J
    zeroC : Zero

    -- Exactness of the essential sequence (stub for now).
    essential-exact : Set (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)


-- If the torsion part has an initial object, then in a semidirect cleft the
-- functor X ↦ KL (⊥ , X) is a canonical candidate left adjoint to q.
module _ {a b : Level} {I : Set a} {J : Set b} (sdir : SDirCleft I J)
         (init𝓣 : Initial (FullSubCategory (Cleft.𝓣 (SDirCleft.cleft sdir)))) where

  private
    cleft = SDirCleft.cleft sdir
    FS𝓣 = FullSubCategory (Cleft.𝓣 cleft)
    FS𝓕 = FullSubCategory (Cleft.𝓕 cleft)
    P = Product FS𝓣 FS𝓕

    ⊥𝓣 = Initial.⊥ init𝓣

    L : Functor FS𝓕 P
    L = constˡ {C = FS𝓣} {D = FS𝓕} ⊥𝓣

    R : Functor P FS𝓕
    R = πʳ

    module 𝓣 = Category FS𝓣
    module 𝓕 = Category FS𝓕
    module P = Category P

  constˡ⊥⊣πʳ : L ⊣ R
  constˡ⊥⊣πʳ = record
    { unit   = ntHelper record
      { η       = λ _ → 𝓕.id
      ; commute = λ f → 𝓕.Equiv.trans 𝓕.identityˡ (𝓕.Equiv.sym 𝓕.identityʳ)
      }
    ; counit = ntHelper record
      { η = λ where
        (A , X) → (Initial.! init𝓣 {A = A} , 𝓕.id)
      ; commute = λ where
        {X = (A , X)} {Y = (B , Y)} (fA , fX) →
          ( 𝓣.Equiv.trans 𝓣.identityʳ (Initial.!-unique init𝓣 (fA 𝓣.∘ Initial.! init𝓣 {A = A}))
          , 𝓕.Equiv.trans 𝓕.identityˡ (𝓕.Equiv.sym 𝓕.identityʳ)
          )
      }
    ; zig = λ {X} →
        ( 𝓣.Equiv.trans 𝓣.identityʳ (Initial.⊥-id init𝓣 (Initial.! init𝓣 {A = ⊥𝓣}))
        , 𝓕.identityˡ
        )
    ; zag = λ { {B = (A , X)} → 𝓕.identityˡ }
    }

  private
    KL = SDirCleft.KL sdir
    K  = Cleft.K cleft

    qL : Functor FS𝓕 C
    qL = KL ∘F L

    qL⊣q : qL ⊣ (πʳ {C = FS𝓣} {D = FS𝓕} ∘F K)
    qL⊣q =
      constˡ⊥⊣πʳ ∘⊣ SDirCleft.KL⊣K sdir

  Sdir=>Split : SplitCleft I J
  Sdir=>Split = record
    { cleft = cleft
    ; qL = qL
    ; qL⊣q = qL⊣q
    }

-- a zero cleft: a cleft where the composite adjunction q∘i ⊣ iR∘qR is the null adjunction,
-- i.e., the subcategories have zero objects and the composites are constant at zero.

record ZeroCleft {a b : Level} (I : Set a) (J : Set b) : Set (o ⊔ ℓ ⊔ e ⊔ a ⊔ b) where
  field
    cleft : Cleft I J
    ⊥𝓣   : Initial (FullSubCategory (Cleft.𝓣 cleft))
    ⊤𝓣   : Terminal (FullSubCategory (Cleft.𝓣 cleft))
    ⊥𝓕   : Initial (FullSubCategory (Cleft.𝓕 cleft))
    ⊤𝓕   : Terminal (FullSubCategory (Cleft.𝓕 cleft))

  private
    FS𝓣 = FullSubCategory (Cleft.𝓣 cleft)
    FS𝓕 = FullSubCategory (Cleft.𝓕 cleft)
    Q∘I  = Cleft.q cleft ∘F Cleft.i cleft
    IR∘QR = Cleft.iR cleft ∘F Cleft.qR cleft

  field
    q∘i-const   : Q∘I ≃ const (Initial.⊥ ⊥𝓕)
    iR∘qR-const : IR∘QR ≃ const (Terminal.⊤ ⊤𝓣)

-- null adjunction: between any two categories each with an initial and a terminal object,
-- the constant functor at D's initial is left adjoint to the constant functor at C's terminal.

module _ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′}
  (initC : Initial C) (termC : Terminal C)
  (initD : Initial D) (termD : Terminal D) where

  private
    ⊥D = Initial.⊥ initD
    ⊤C = Terminal.⊤ termC

  L : Functor C D
  L = const ⊥D

  R : Functor D C
  R = const ⊤C

  private
    module C′ = Category C
    module D′ = Category D
    module L = Functor L
    module R = Functor R

  nullUnit : NaturalTransformation idF (R ∘F L)
  nullUnit = ntHelper record
    { η = λ X → Terminal.! termC {X}
    ; commute = λ {X Y} f → C′.Equiv.trans
      (C′.Equiv.sym (termC .Terminal.!-unique (Terminal.! termC {Y} C′.∘ f)))
      (C′.Equiv.sym (C′.identityˡ {f = Terminal.! termC {X}}))
    }

  nullCounit : NaturalTransformation (L ∘F R) idF
  nullCounit = ntHelper record
    { η = λ Y → Initial.! initD {Y}
    ; commute = λ {X Y} f → D′.Equiv.trans
      (D′.identityʳ {f = Initial.! initD {Y}})
      (initD .Initial.!-unique (f D′.∘ Initial.! initD {X}))
    }

  nullAdj : L ⊣ R
  nullAdj = record
    { unit   = nullUnit
    ; counit = nullCounit
    ; zig    = λ {A} → D′.Equiv.trans
      (D′.identityʳ {f = NaturalTransformation.η nullCounit (L.F₀ A)})
      (initD .Initial.!-unique D′.id)
    ; zag    = λ {B} → C′.Equiv.trans
      (C′.identityˡ {f = NaturalTransformation.η nullUnit (R.F₀ B)})
      (termC .Terminal.!-unique C′.id)
    }
