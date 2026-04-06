---
name: lean-olympiad-geometry-proof
description: 'Formalize plane Euclidean olympiad geometry proofs in Lean and mathlib4. Use when translating synthetic proofs about cyclic points, equal angles, same-side conditions, similar triangles, power-of-a-point, and distance ratios into a stable configuration-first proof.'
argument-hint: 'Describe the geometry statement, the intended synthetic proof idea, and any partial Lean code or failing lemmas.'
---

# Lean Olympiad Geometry Proof

## When to Use
- Formalizing planar Euclidean geometry olympiad problems in Lean.
- Turning a handwritten angle-chasing or similarity proof into a robust mathlib proof.
- Repairing a partially written geometry file that already has a configuration structure and some local lemmas.
- Converting ratio statements into distance equalities after a similarity argument.
- Reworking a proof that is already half-formalized but has `sorry` placeholders or API mismatches.

## Core Strategy
Work from configuration to invariants to metric conclusion.

1. Normalize the ambient assumptions first.
2. Package the problem data into a `Cfg` structure if the statement has many hypotheses.
3. Prove low-level distinctness, non-collinearity, and side-of-line lemmas before touching the main theorem.
4. Isolate the angle step from the metric step.
5. Use similarity to produce proportional distance equalities.
6. Finish with short algebra on distances, not with more geometry.

## Procedure

### 1. Normalize the ambient geometry
- If the proof uses oriented angles, add `[Fact (finrank ℝ V = 2)]` and `[Module.Oriented ℝ V (Fin 2)]` early.
- Keep `attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two` near the top so two-dimensional APIs elaborate reliably.
- Import only the geometry modules you actually need, then add metric or convex imports only after the geometric spine is clear.

### 2. Encode the handwritten proof as a lemma chain
- Write the informal proof outline as comments first.
- Turn each conceptual step into one theorem inside `Cfg`.
- Prefer short theorems with names that reflect the mathematical step, such as `cospherical_pts`, `angle_step`, or `length_conclusion`.
- Keep the order aligned with the human proof so diagnostics remain local.

### 3. Build the configuration layer aggressively
- Prove all easy inequalities early: `A_ne_B`, `P_ne_A`, `D_ne_B`, and similar.
- Derive non-collinearity from affine independence once, then reuse it.
- When a point is on the same side of a line, extract `notMem` consequences immediately. These often unlock later affine-independence proofs.
- For cyclic or cospherical statements, prove membership in one chosen sphere instead of reconstructing a circle from scratch.

### 4. Handle the angle step in two layers
- First prove the oriented-angle identity if the theorem is really an inscribed-angle or same-side statement.
- Then convert to an unoriented-angle equality only when the similarity theorem requires it.
- A reliable pattern is:
  1. prove `two_zsmul` equality from cospherical points,
  2. prove sign equality from `SSameSide`,
  3. use `Real.Angle.two_zsmul_eq_iff_eq`,
  4. convert with `angle_eq_abs_oangle_toReal`.

### 5. Use similarity as the bridge to metric algebra
- If you already have two angle equalities, target `similar_of_angle_angle`.
- After similarity, prefer `exists_pos_dist_eq` over manually unpacking ratio theorems.
- This gives a single scaling factor `r` and distance equations that are easy to reuse.
- If the target is a ratio like `PB = 2 * PD`, look for a more invariant equation first, then simplify at the end.

### 6. Finish metric conclusions with positivity-aware algebra
- Distances are nonnegative, and distinct points give positivity through `dist_pos.mpr`.
- Once similarity yields proportional equalities, reduce the final step to `nlinarith` whenever possible.
- If you get equality of squares, split with `sq_eq_sq_iff_eq_or_eq_neg`, discard the negative branch using nonnegativity, then conclude.

## Common Pitfalls
- Missing `[Fact (finrank ℝ V = 2)]` is a common cause of oriented-angle failures and long elaboration time.
- `SSameSide.oangle_sign_eq` is used on the hypothesis term itself, not as a field projected from the predicate family.
- `angle_eq_abs_oangle_toReal` is sensitive to argument order. Supply the endpoint inequalities in the order expected by the angle vertex.
- Set-valued collinearity or cospherical goals often differ only by insertion order. Use `simpa [Set.insert_comm, Set.pair_comm]` rather than reproving them.
- Do not try to finish the entire theorem directly from the final goal. Prove the geometric spine first, then the algebraic tail.
- If the current theorem is stuck on a `sorry`, inspect the surrounding lemmas before changing the main proof. The fix is often one missing bridge lemma, not a rewrite of the whole file.

## Working Style
- Prefer one geometric fact per theorem.
- Keep theorem names local and literal rather than overly abstract.
- If a proof step is a standard olympiad pattern, encode that pattern directly instead of hiding it inside one large `by` block.
- Use the Lean diagnostics loop early. Geometry files become expensive to debug if several broken steps accumulate.

## Reference
- See [geometry proof framework](./references/geometry-framework.md) for a reusable decomposition and a mapping from synthetic steps to Lean lemmas.
