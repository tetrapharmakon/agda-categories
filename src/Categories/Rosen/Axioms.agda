{-# OPTIONS --without-K --warning=noUserWarning --warning=noUselessPrivate --warning=noUnsupportedIndexedMatch #-}

-- The axioms assumed by the Categories.Rosen development.
--
-- This module exists so that the development's non-logical assumptions are
-- collected in exactly one place, and so that `grep -rn Rosen.Axioms` lists
-- every module that depends on one.  It is deliberately tiny.
--
-- What is here is an ORDINARY AXIOM: consistent with Agda's type theory, and
-- of the kind mathematicians assume without comment.  It is not a placeholder
-- for a missing proof, and it is the ONLY postulate in Categories.Rosen: a
-- `grep -rn postulate src/Categories/Rosen/` returns this line and nothing else.
--
-- Keep it that way.  Statements this development finds to be false are recorded
-- by removing them and documenting the obstruction where they stood, not by
-- postulating them; several such postulates existed for a while and each one
-- put a name asserting a falsehood into the tree.
--
-- Consequence to be aware of: any module in the transitive closure of this one
-- cannot be checked with --safe.  Today that is Cartesian/Sets.agda and
-- everything instantiated over Sets through it.
module Categories.Rosen.Axioms where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Function extensionality: two pointwise-equal dependent functions are equal.
--
-- Needed because Sets in agda-categories has _≈_ = pointwise propositional
-- equality on the *elements*, while the Cartesian-closed structure has to
-- produce equalities between the *functions* themselves (curry-resp-≈,
-- curry-unique, and the naturality squares in Coherent/C2Sets.agda).
postulate
  extensionality : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
                 → (∀ x → f x ≡ g x) → f ≡ g
