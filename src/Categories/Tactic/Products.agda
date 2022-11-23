{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- A simple reflection based solver for categories.
--
-- Based off 'Tactic.MonoidSolver' from 'agda-stdlib'
--------------------------------------------------------------------------------

open import Categories.Category

module Categories.Tactic.Products where

open import Level
open import Function using (_⟨_⟩_)

open import Data.Bool    as Bool    using (Bool; _∨_; if_then_else_)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing; maybe)
open import Data.List    as List    using (List; _∷_; [])

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Instance.One renaming (One to ⊤; One-op to ⊤-op)
open import Categories.Category.Monoidal.Instance.Cats
open import Categories.Category.Instance.Cats
open import Categories.Category.Monoidal
import Categories.Morphism

open import Agda.Builtin.Reflection
open import Reflection.Argument
open import Reflection.Term using (getName; _⋯⟅∷⟆_)
open import Reflection.TypeChecking.Monad.Syntax

module _ {o ℓ e} where

  private
    variable
      A B C : Category o ℓ e

  open Monoidal (Product.Cats-Monoidal {o} {ℓ} {e})
  open BinaryProducts (Product.Cats-has-all {o} {ℓ} {e})
  open import Categories.Morphism (Cats o ℓ e)
  open import Relation.Binary.Reasoning.Setoid ≅-setoid

  --------------------------------------------------------------------------------
  -- An 'Expr' reifies the parentheses/identity morphisms of some series of
  -- compositions of morphisms into a data structure. In fact, this is also
  -- a category!
  --------------------------------------------------------------------------------
  data Expr : Set (suc (o ⊔ ℓ ⊔ e)) where
    _×′_ : Expr → Expr → Expr
    1′   : Expr
    op′_ : Expr → Expr
    [_↑] : Category o ℓ e → Expr

  -- Embed a morphism in 'Expr' back into '𝒞' without normalizing.
  [_↓] : Expr → Category o ℓ e
  [ c ×′ d ↓] = [ c ↓] × [ d ↓]
  [ 1′     ↓] = ⊤
  [ [ c ↑] ↓] = c
  [ op′ c  ↓] = Category.op [ c ↓]

  -- Convert an 'Expr' back into a morphism, while normalizing
  --
  -- This actually embeds the morphism into the category of copresheaves
  -- on 𝒞, which obeys the category laws up to beta-eta equality.
  -- This lets us normalize away all the associations/identity morphisms.
  mutual
    embed : Expr → Category o ℓ e → Category o ℓ e
    embed (c ×′ d) e = embed c (embed d e)
    embed 1′ c = c
    embed [ c ↑] d = c × d
    embed (op′ c) d = embedᵒᵖ c d

    embedᵒᵖ : Expr → Category o ℓ e → Category o ℓ e
    embedᵒᵖ (c ×′ d) e = embedᵒᵖ c (embedᵒᵖ d e)
    embedᵒᵖ 1′ c = c
    embedᵒᵖ [ c ↑] d = Category.op c × d
    embedᵒᵖ (op′ c) d = embed c d

  mutual
    preserves-≈′ : ∀ (t : Expr) → (c : Category o ℓ e) → embed t ⊤ × c ≅ embed t c
    preserves-≈′ (c ×′ c') d = begin
      embed (c ×′ c') ⊤ × d        ≡⟨⟩
      embed c (embed c' ⊤) × d     ≈⟨ ×-cong (≅.sym (preserves-≈′ c (embed c' ⊤))) ≅.refl ⟩
      (embed c ⊤ × embed c' ⊤) × d ≈⟨ ≅.sym ×-assoc ⟩
      embed c ⊤ × (embed c' ⊤ × d) ≈⟨ ×-cong ≅.refl (preserves-≈′ c' d) ⟩
      embed c ⊤ × (embed c' d)     ≈⟨ preserves-≈′ c _ ⟩
      embed c (embed c' d)         ∎
    preserves-≈′ 1′ d     = unitorˡ
    preserves-≈′ [ c ↑] d = ×-cong unitorʳ ≅.refl
    preserves-≈′ (op′ c)  = preservesᵒᵖ-≈′ c

    preservesᵒᵖ-≈′ : ∀ (t : Expr) → (c : Category o ℓ e) → embedᵒᵖ t ⊤ × c ≅ embedᵒᵖ t c
    preservesᵒᵖ-≈′ (c ×′ c') d = begin
      embedᵒᵖ (c ×′ c') ⊤ × d          ≡⟨⟩
      embedᵒᵖ c (embedᵒᵖ c' ⊤) × d     ≈⟨ ×-cong (≅.sym (preservesᵒᵖ-≈′ c (embedᵒᵖ c' ⊤))) ≅.refl ⟩
      (embedᵒᵖ c ⊤ × embedᵒᵖ c' ⊤) × d ≈⟨ ≅.sym ×-assoc ⟩
      embedᵒᵖ c ⊤ × (embedᵒᵖ c' ⊤ × d) ≈⟨ ×-cong ≅.refl (preservesᵒᵖ-≈′ c' d) ⟩
      embedᵒᵖ c ⊤ × (embedᵒᵖ c' d)     ≈⟨ preservesᵒᵖ-≈′ c _ ⟩
      embedᵒᵖ c (embedᵒᵖ c' d)         ∎
    preservesᵒᵖ-≈′ 1′ d       = unitorˡ
    preservesᵒᵖ-≈′ [ c ↑] d   = ×-cong unitorʳ ≅.refl
    preservesᵒᵖ-≈′ (op′ c)    = preserves-≈′ c

  mutual
    correct : ∀ (t : Expr) → embed t ⊤ ≅ [ t ↓]
    correct 1′ = ≅.refl
    correct (op′ t) = preservesᵒᵖ-≈ t
    correct [ x ↑] = unitorʳ
    correct (d₁ ×′ d₂) = begin
      embed (d₁ ×′ d₂) ⊤      ≡⟨⟩
      embed d₁ (embed d₂ ⊤)   ≈⟨ ≅.sym (preserves-≈′ d₁ (embed d₂ ⊤)) ⟩
      embed d₁ ⊤ × embed d₂ ⊤ ≈⟨ ×-cong (correct d₁) (correct d₂) ⟩
      [ d₁ ↓] × [ d₂ ↓]       ≡⟨⟩
      [ d₁ ×′ d₂ ↓]           ∎

    preservesᵒᵖ-≈ : ∀ (t : Expr) → embedᵒᵖ t ⊤ ≅ Category.op [ t ↓]
    preservesᵒᵖ-≈ 1′ = ≅.refl
    preservesᵒᵖ-≈ (op′ t) = correct t
    preservesᵒᵖ-≈ [ x ↑] = ≅.trans (×-cong ≅.refl ⊤-op) unitorʳ
    preservesᵒᵖ-≈ (d₁ ×′ d₂) = begin
      embedᵒᵖ (d₁ ×′ d₂) ⊤        ≡⟨⟩
      embedᵒᵖ d₁ (embedᵒᵖ d₂ ⊤)   ≈⟨ ≅.sym (preservesᵒᵖ-≈′ d₁ (embedᵒᵖ d₂ ⊤)) ⟩
      embedᵒᵖ d₁ ⊤ × embedᵒᵖ d₂ ⊤ ≈⟨ ×-cong (preservesᵒᵖ-≈ d₁) (preservesᵒᵖ-≈ d₂)  ⟩
      Category.op [ d₁ ↓] × Category.op [ d₂ ↓] ≡⟨⟩
      Category.op [ d₁ ×′ d₂ ↓]                 ∎

--------------------------------------------------------------------------------
-- Reflection Helpers
--------------------------------------------------------------------------------

module _ {o ℓ e} where

  open import Data.Product renaming (_×_ to _×'_)

  open BinaryProducts (Product.Cats-has-all {o} {ℓ} {e})
  open import Categories.Morphism (Cats o ℓ e)
  open import Relation.Binary.Reasoning.Setoid ≅-setoid

  --------------------------------------------------------------------------------
  -- Reflection Helpers
  --------------------------------------------------------------------------------

  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

  getArgs : Term → Maybe (Term ×' Term)
  getArgs (def _ xs) = go xs
    where
    go : List (Arg Term) → Maybe (Term ×' Term)
    go (vArg x ∷ vArg y ∷ []) = just (x , y)
    go (x ∷ xs) = go xs
    go _ = nothing
  getArgs _ = nothing

  --------------------------------------------------------------------------------
  -- Constructing an Expr
  --------------------------------------------------------------------------------

  ″1″ : Term
  ″1″ = quote 1′ ⟨ con ⟩ []

  ″[_↑]″ : Term → Term
  ″[ t ↑]″ = quote [_↑] ⟨ con ⟩ (t ⟨∷⟩ [])

  ″op_″ : Term → Term
  ″op t ″ = quote op′_ ⟨ con ⟩ (t ⟨∷⟩ [])

  open import Categories.Category.Product

  is-×  = λ x → x == quote Product
  is-id = λ x → x == quote ⊤
  is-op = λ x → x == quote Category.op

  mutual
    ″×″-help : List (Arg Term) → Term
    ″×″-help (x ⟨∷⟩ y ⟨∷⟩ xs) = quote _×′_ ⟨ con ⟩ buildExpr x ⟨∷⟩ buildExpr y ⟨∷⟩ []
    ″×″-help (x ∷ xs) = ″×″-help xs
    ″×″-help [] = unknown

    ″op″-help : List (Arg Term) → Term
    ″op″-help (x ⟨∷⟩ xs) = quote op′_ ⟨ con ⟩ buildExpr x ⟨∷⟩ []
    ″op″-help (x ∷ xs) = ″op″-help xs
    ″op″-help [] = unknown

    buildExpr : Term → Term
    buildExpr t@(def n xs) =
      if (is-× n)
        then ″×″-help xs
      else if (is-id n)
        then ″1″
      else if (is-op n)
        then ″op″-help xs
      else
        ″[ t ↑]″
    buildExpr t = ″[ t ↑]″

  --------------------------------------------------------------------------------
  -- Constructing the Solution
  --------------------------------------------------------------------------------

  constructSoln : Term → Term → Term
  constructSoln lhs rhs =
    quote ≅.trans ⟨ def ⟩
      (quote ≅.sym ⟨ def ⟩
        (quote correct ⟨ def ⟩ lhs ⟨∷⟩ []) ⟨∷⟩ [])
      ⟨∷⟩ (quote correct ⟨ def ⟩ rhs ⟨∷⟩ [])
      ⟨∷⟩ []

  solve-macro : Term → TC _
  solve-macro hole = do
    hole′ ← inferType hole >>= normalise
    just (lhs , rhs) ← returnTC (getArgs hole′)
      where nothing → typeError (termErr hole′ ∷ [])
    let soln = constructSoln (buildExpr lhs) (buildExpr rhs)
    unify hole soln

  macro
    solve : Term → TC _
    solve = solve-macro

  base : ∀ {a b c : Category o ℓ e}
       → Category.op a × ⊤ × Category.op (Category.op b) ≅ Category.op ((⊤ × a) × Category.op b)
  base = solve
