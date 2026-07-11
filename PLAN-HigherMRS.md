# HigherMRS Refactoring Plan

Target: `src/Categories/Rosen/HigherMRS.agda`

## Goal

Close the remaining holes by making each downward map carry both its functor and a functorial compatibility natural isomorphism

```agda
V m ∘F F-down ≃ V n
```

The compatibility must be coherent with the reflexive downward map. In particular, for the reflexive case it must agree with the whiskered identity isomorphism

```agda
V n ⓘʳ lemma-id
```

Otherwise the `IsoComma` commute proof in `lemma-id` is not derivable.

## Steps

1. Normalize the level Arrow functors. Define each successor Arrow functor as the composition of the previous Arrow functor with `Π-MRS`, or provide an explicit `V-step` natural isomorphism when the definitions are not judgmentally equal.
2. Define a reusable `lift` helper. Given a functor `F` and a natural isomorphism `α : V m ∘F F ≃ V n`, it constructs the successor-level IsoComma functor. Its object iso uses the inverse component of `α`; its morphism commute proof uses `α.⇒.commute` and the original IsoComma square.
3. Define `lift-compat`, proving that the lifted functor has the required successor-level Arrow compatibility. Compose `V-step`, whiskered `α`, projection coherence, associators, and unitors.
4. Separate the reflexive downward construction. Define the reflexive functor recursively and choose its compatibility as `V n ⓘʳ lemma-id`, using mutual recursion only over the lower level. Use this coherent construction for `downF {n} {n} ≤-refl`.
5. Use `lift` and `lift-compat` to define the general downward map. Keep the public result as a sigma containing the functor and compatibility natural isomorphism; expose projections for the chain construction.
6. Close `lemma-id` using the coherent reflexive compatibility. The two IsoComma commute holes should reduce to the square of the whiskered natural isomorphism, with identity on the `ElMRS` coordinate.
7. Define a generic `lift-compose` natural isomorphism. Use it to close all branches of `lemma-homomorphism` instead of proving the successor cases independently.
8. Canonicalize or otherwise factor proof irrelevance for the thin natural-number category. Use that helper to close `lemma-Fresp`.
9. Rebuild `MRS-chain` from the projected downward functor and typecheck the entire module.

## Verification Order

Typecheck after each of these milestones:

1. `V-step` and `lift`
2. `lift-compat`
3. Reflexive downward maps and `lemma-id`
4. `lift-compose` and `lemma-homomorphism`
5. `lemma-Fresp` and `MRS-chain`

Remove `--allow-unsolved-metas` once the module is complete.

## Session Log

### 2026-07-11 — Eliminate `--allow-unsolved-metas`

**Attempted:** Remove `--allow-unsolved-metas` to enforce full proof.
**Result:** 8 unsolved metas (explicit composition arguments in `Arr.Arrow` reasoning) and 14 interaction metas (the `{! !}` holes). Not viable without completing the proofs.

**Restored** `--allow-unsolved-metas`.  Plan is to continue closing holes one at a time, starting with `lemma-id {suc n}`.

## Future Work

- Close `lemma-id {suc n}`: fill the two `IsoComma⇒.commute` fields using the coherent compatibility isomorphism.
- Build `lift` / `lift-compose` helpers to close `lemma-homomorphism`.
- Provide canonicalization or proof-irrelevance lemma for thin categories to close `lemma-Fresp`.
- Remove `--allow-unsolved-metas` after all holes are closed.
