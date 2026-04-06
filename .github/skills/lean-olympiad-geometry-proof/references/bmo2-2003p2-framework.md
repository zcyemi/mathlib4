# BMO2 2003 P2 Framework

This note records the proof skeleton used in `Archive/TrainingSet/BMO2_2003P2.lean` and extracts the parts that are reusable.

## High-Level Shape

1. Package all data into `Cfg`.
2. Prove point distinctness and non-collinearity.
3. Show `A, B, C, P` are cospherical by placing all four points on the triangle circumsphere.
4. Derive the inscribed-angle equality.
5. Combine that with the collinearity of `A, D, B` to get triangle similarity.
6. Extract distance equalities from `Similar.exists_pos_dist_eq`.
7. Convert the given relation `4 * AD = AB` into `AP = 2 * AD`.
8. Feed that back into the similarity scale to conclude `PB = 2 * PD`.

## Recommended Theorem Order

Use the following ordering when writing a file of this shape.

1. Configuration facts.
2. Circle or sphere membership facts.
3. Oriented-angle sign and doubling facts.
4. Unoriented-angle equalities.
5. Similarity theorem.
6. Distance-scale theorem.
7. Final algebraic consequences.

## Why This Order Works

- Configuration lemmas shrink later goals.
- The circle step is isolated and reusable.
- The angle section becomes a small self-contained block.
- Similarity becomes the only place where the two angle equalities are consumed.
- Metric algebra happens after geometry is finished, so there is less interleaving between theorem families.

## Useful Proof Moves

### Cospherical step
Do not construct a new sphere. Reuse the triangle circumsphere and prove a subset relation pointwise.

### Inscribed-angle step
For cyclic points, prefer the oriented-angle route:

1. `two_zsmul_oangle_eq`
2. sign equality from same-side information
3. `Real.Angle.two_zsmul_eq_iff_eq`
4. `angle_eq_abs_oangle_toReal`

This is more stable than trying to prove the unoriented-angle equality directly.

### Similarity step
If the handwritten proof says "AA similarity", mirror that literally using `similar_of_angle_angle`.
Then immediately ask similarity for distance equations, instead of proving separate ratio lemmas by hand.

### Final metric step
Once you have

- `AD = r * AP`,
- `AP = r * AB`,
- `DP = r * PB`,

the rest is algebra. Keep the final theorems short and let `nlinarith` handle the arithmetic side conditions.

## Reusable Lessons for Similar Problems

- In olympiad geometry formalization, the real bottleneck is usually not the last equation. It is identifying the correct intermediate objects: same-side hypotheses, cyclicity witnesses, and a usable similarity statement.
- Split "angle chase" from "length chase". Trying to mix them usually produces brittle proofs.
- Comments that mirror the paper proof are worth keeping if they explain the theorem order.
- If you later formalize a problem in the style of IMO 2019 P2, keep the same discipline: package the configuration, expose the invariant geometric facts first, and only then push them into the final metric or incidence statement.
