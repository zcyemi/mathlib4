# Geometry Proof Framework

This note records a reusable proof skeleton for planar Euclidean olympiad geometry in Lean.

## Generic Proof Shape

1. Package the data into a configuration structure.
2. Prove the easy separation facts first: distinctness, non-collinearity, and side-of-line statements.
3. Build the cyclic or cospherical invariant.
4. Convert the invariant into angle equalities.
5. Derive a similarity statement.
6. Extract distance ratios or proportional equalities.
7. Finish with algebra on distances.

## Generic Theorem Ordering

For a well-structured geometry file, the order usually looks like this:

1. Configuration facts.
2. Line and side lemmas.
3. Cyclicity or sphere membership.
4. Oriented-angle lemmas.
5. Unoriented-angle lemmas.
6. Similarity or congruence lemmas.
7. Length or ratio lemmas.
8. Final statement.

## Reusable Patterns

### Cyclic / cospherical data
- Use one fixed circle or sphere and prove all required points lie on it.
- Reuse the hypothesis set directly when possible.
- If a theorem expects a set equality up to insertion order, use `simpa [Set.insert_comm, Set.pair_comm]`.

### Angle data
- Prefer oriented angles when signs or same-side information are available.
- Use the sign of oriented angles to control which branch of a doubling lemma you are in.
- Convert to unoriented angles only when a similarity theorem needs it.

### Similarity data
- If the informal proof says “AA similarity”, encode that literally with `similar_of_angle_angle`.
- After similarity, ask for the distance equations immediately.
- Keep the similarity theorem small and let later lemmas consume it.

### Metric conclusion
- Once you have proportional equalities, isolate the algebraic statement as a separate theorem.
- Use positivity of distances and `nlinarith` or square-equality lemmas to eliminate unwanted branches.

## Debugging Heuristics

- If elaboration fails, first check whether a missing `Fact (finrank ℝ V = 2)` or local instance is the cause.
- If a theorem name exists but the call fails, inspect the argument order rather than the theorem statement.
- If the proof is getting large, split it into configuration, angle, similarity, and metric layers.
- If the current file is already partially formalized, repair the bridge lemmas before touching the final theorem.

## Reuse Across Problems

This framework is intended for future geometry problems, including IMO-style angle chase and ratio problems, as well as any planar Euclidean proof that naturally breaks into cyclicity, similarity, and distance algebra.
