---
name: lean-olympiad-geometry-proof
description: 'Formalize plane Euclidean olympiad geometry proofs in Lean and mathlib4. Use when translating synthetic proofs about cyclic points, equal angles, same-side conditions, similar triangles, power-of-a-point, and distance ratios into a stable configuration-first proof, with incremental lemma landing and temporary `sorry` placeholders when a local subgoal stalls.'
argument-hint: 'Describe the geometry statement, the intended synthetic proof idea, and any partial Lean code or failing lemmas.'
---

# Lean Olympiad Geometry Proof

Use this skill when writing Lean proofs for Euclidean geometry competition problems.

## When to Use
- Formalizing planar Euclidean geometry olympiad problems in Lean.
- Turning a handwritten angle-chasing or similarity proof into a robust mathlib proof.
- Repairing a partially written geometry file that already has a configuration structure and some local lemmas.
- Converting ratio statements into distance equalities after a similarity argument.
- Reworking a proof that is already half-formalized but has `sorry` placeholders or API mismatches.

## Scope
- Prefer synthetic geometry reasoning.
- Avoid building coordinate systems, introducing explicit point coordinates, or turning the problem into an analytic geometry solution unless the user explicitly asks for that style.
- Vector and inner-product calculations are allowed when they are a natural part of the synthetic argument.
- Keep the proof close to the geometry: incidence, collinearity, side relations, angle equalities, similarity, power of a point, tangency, and distance decompositions.

## Core Strategy
Work from configuration to invariants to metric conclusion.

1. Normalize the ambient assumptions first.
2. Package the problem data into a `Cfg` structure if the statement has many hypotheses.
3. Prove low-level distinctness, non-collinearity, and side-of-line lemmas before touching the main theorem.
4. Isolate the angle step from the metric step.
5. Use similarity to produce proportional distance equalities.
6. Finish with short algebra on distances, not with more geometry.
7. If a local lemma does not yield after a few targeted attempts, park it with a temporary `sorry`, continue proving the surrounding spine, and come back once the dependency chain is in place.

## Default Proof Shape

Write the file in a 2003P2-style layered structure:

1. Put all given objects and hypotheses into a bundled configuration `Cfg` structure.
2. Add a `namespace Cfg` and work from `variable (cfg : Cfg ...)`.
3. Prove local geometric facts as named theorems inside the namespace.
4. Group them by meaning, not by tactical convenience:
   - configuration properties
   - angle or side lemmas
   - similarity or congruence lemmas
   - length or power relations
   - final algebraic reduction
5. End with one thin wrapper theorem that constructs `cfg` and calls `cfg.result`.

## Standard Template

```lean
structure Cfg where
  (A B C D P : Pt)
  (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
  {triangle_ABC : Triangle ℝ Pt}
  (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
  -- add the geometry-specific hypotheses here

namespace Cfg

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

variable (cfg : Cfg (V := V) (Pt := Pt))

/-! ### Configuration properties -/

theorem A_ne_B : cfg.A ≠ cfg.B := by
  -- derive nondegeneracy from affine independence / side assumptions
  sorry

/-! ### Main geometric step -/

theorem some_angle_eq : ∠ cfg.A cfg.P cfg.B = ∠ cfg.A cfg.C cfg.B := by
  -- use circle, side, or similarity arguments
  sorry

/-! ### Length relations -/

theorem some_dist_eq : dist cfg.P cfg.B = 2 * dist cfg.P cfg.D := by
  -- combine similarity, power, or secant/tangent relations
  sorry

theorem result : target_statement := by
  -- final short algebraic reduction
  sorry

end Cfg

theorem result {A B C D P : Pt} ... : target_statement := by
  let cfg : Cfg (V := V) (Pt := Pt) :=
    ⟨...⟩
  simpa using cfg.result
```

## Procedure

### 1. Normalize the ambient geometry
- If the proof uses oriented angles, add `[Fact (finrank ℝ V = 2)]` and `[Module.Oriented ℝ V (Fin 2)]` early.
- Keep `attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two` near the top so two-dimensional APIs elaborate reliably.
- Import only the geometry modules you actually need, then add metric or convex imports only after the geometric spine is clear.

### 1.5. Use the available Lean tooling
- If the environment provides MCP tools such as `lean_explore` and `lean_submit_proof`, use them to search declarations and to assess proof readiness before or after landing substantial geometry lemmas.
- Use the diagnostics loop early when the environment exposes it; do not let several broken geometry steps accumulate before checking them.

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
- For cyclic quadrilaterals, the fastest route is often: build one `Cospherical` witness, use `two_zsmul_oangle_eq` on the sphere, then normalize set membership with `simpa [Set.insert_comm, Set.pair_comm]`.
- For same-side hypotheses, move from `SSameSide` to the sign statement directly, as in `oangle_sign_eq` or `oangle_sign_eq_zero_iff_collinear`, instead of trying to reprove the geometric picture.

### 5. Use similarity as the bridge to metric algebra
- If you already have two angle equalities, target `similar_of_angle_angle`.
- After similarity, prefer `exists_pos_dist_eq` over manually unpacking ratio theorems.
- This gives a single scaling factor `r` and distance equations that are easy to reuse.
- If the target is a ratio like `PB = 2 * PD`, look for a more invariant equation first, then simplify at the end.
- When the goal is a secant/tangent or power-of-a-point relation, check `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant` and the `mul_dist_eq_abs_power` family before doing bespoke algebra.
- For segment decompositions on a line, the pair `angle_eq_pi_iff_sbtw` and `dist_eq_add_dist_of_angle_eq_pi` is often the cleanest way to turn betweenness into linear distance equations.

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
- Do not introduce `axiom` placeholders in proof files. If a lemma is not yet proved, isolate the missing step explicitly or use a temporary `sorry` while preserving the proof spine.
- If a local proof step is stuck after several focused attempts, leave a temporary `sorry` and move on. The point is to keep the already-understood spine in the file, not to lose it while searching for one missing bridge.
- Before finishing, return to every temporary `sorry`, prove each one, and then do a final pass over the chain to check that the written proof still matches the intended geometry.

## Allowed Patterns
- `AffineIndependent` and `Triangle` to package the nondegenerate triangle.
- `Sbtw`, `SSameSide`, `SOppSide`, and `Collinear` to control incidence and orientation.
- `∠` and `∡` lemmas for angle transport.
- `similar_of_angle_angle` and related similarity lemmas.
- `Sphere.IsTangentAt`, `Sphere.mul_dist_eq_abs_power`, and secant-tangent relations.
- Vector identities such as `vsub`, `smul`, `inner`, and orthogonality when they match the geometric picture.

## Avoid
- Coordinate constructions unless the user explicitly asks for analytic geometry.
- Solving by embedding points into explicit coordinates or matrices.
- Jumping straight to `nlinarith` before the geometric structure is in place.
- Large one-shot proofs that hide the geometry.
- Mixing unrelated lemmas into the main theorem when they can be named and reused.

## Helpful Tactics and Moves
- Use `simpa` after an equality of lines, circles, affine spans, or set insertions that differ only by ordering.
- Use `rw` to replace a line or a triangle by an equivalent definition from the configuration.
- Use `have` blocks for each geometric milestone.
- Use `calc` chains to keep algebra readable.
- Use `nlinarith` only after the needed geometric equalities are established.
- Use `ring` only for polynomial rearrangements in the final length step.

## Working Style
- Prefer one geometric fact per theorem.
- Keep theorem names local and literal rather than overly abstract.
- If a proof step is a standard olympiad pattern, encode that pattern directly instead of hiding it inside one large `by` block.
- Use the Lean diagnostics loop early. Geometry files become expensive to debug if several broken steps accumulate.
- When a theorem is proved, write it down immediately instead of keeping it only in working memory. This prevents a finished step from being lost while you chase a later subgoal.
- Before closing the file, reread the proof order once and verify that the intermediate lemmas were landed in a coherent sequence, with no stranded temporary placeholders.

## Completion Check

Before finishing a proof, confirm that:

- every hypothesis is either used directly or clearly justified as auxiliary data,
- every nontrivial geometric claim has a named lemma,
- the final theorem is a short wrapper around `cfg.result`,
- the file compiles without new errors,
- the structure still reads like a geometry proof, not an algebraic elimination script,
- no proof obligation was discharged by `axiom`,
- every temporary `sorry` introduced during exploration has been revisited before finalizing the file.

## Reusable Theorem Patterns From Training Files
- `BMO2_2003P2`: combine `cospherical_ABCP` with `two_zsmul_oangle_eq`, then use same-side sign equality and `Real.Angle.two_zsmul_eq_iff_eq` to move from oriented to unoriented angles; close the metric step via `similar_of_angle_angle` and `exists_pos_dist_eq`.
- `BMO2_2004P1`: if a circle is tangent at a point on a side, first rewrite the supporting line with `affineSpan_pair_eq_of_mem_of_mem_of_ne`, then use `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant` for the tangent-secant relation and `dist_eq_add_dist_of_angle_eq_pi` for collinear segment decomposition.
- `Imo2019Q2`: build the auxiliary intersection points with `Sphere.secondInter`, prove the key cyclicity with `two_zsmul_oangle_eq` on a chosen circumsphere, and use symmetry (`cfg.symm`) aggressively to avoid duplicating the second half of the argument.

## Ongoing Extensions

This skill is intended to grow. Add new proof patterns here when they recur:

- angle chasing with cyclic quadrilaterals,
- similarity chains,
- tangent-secant and power-of-a-point arguments,
- midpoint and perpendicular bisector constructions,
- altitude and orthogonality arguments,
- vector or inner-product lemmas that shorten synthetic arguments without turning them analytic.

## Reference
- See [geometry proof framework](./references/geometry-framework.md) for a reusable decomposition and a mapping from synthetic steps to Lean lemmas.


## 其他约束
- 在进行证明之前先分析题目的形式化是否和自然语言描述匹配是否有不正确的地方，如果有请指出并使用askQuestion询问用户是否需要修改题目描述，然后再进行证明。可以使用python验证点和结论的正确性。
- **重要**明确在Lean的证明中不要使用坐标方式进行证明，目前也Mathlib4也不支持坐标构建方式。优先使用角追等合成几何方法进行证明。
- 最终证明不要使用get_errors进行验证，而必须使用`lean_submit_proof`进行验证。
- **重要**不允许修改 maxHeartbeats的值，如果证明搜索超时表示需要重写证明，将具体的证明步骤分解从而减少搜索空间。
