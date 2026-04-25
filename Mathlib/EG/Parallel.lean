/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib

open scoped Real EuclideanGeometry Similar Congruent InnerProductSpace
open Affine EuclideanGeometry Module AffineSubspace InnerProductSpace

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]

/-!
## Parallel Line Lemmas

This file proves generic lemmas about angles formed by parallel lines and transversals:

- **Vector angle helpers**: bridge between vector-space and point-space angles
- **Corresponding angles** (同位角): `angle_corresponding_of_parallel`
- **Ray invariance**: `angle_sbtw_left_eq` (replacing `t` by `u` on the same ray from `v`)
- **Alternate-interior angles**: `angle_alternate_interior_of_parallel`
- **Co-interior angles are supplementary**: `angle_cointerior_eq_pi_of_parallel`
- **Parallelogram side equality**: `dist_of_parallelogram_vsub`
- **Co-oriented equal-side shortcut**: `dist_of_eq_dist_cooriented`
- **Co-interior angles → parallel**: `parallel_of_cointerior_angles`

These lemmas are intended to package reusable parallel-line facts in a form convenient for later
synthetic geometry proofs.
-/

namespace EuclideanGeometry

/-! ### Vector angle helpers -/

/-- The unoriented angle is invariant under negation of all three arguments:
`∠ (-v₁) 0 (-v₃) = ∠ v₁ 0 v₃` in any real inner product space. -/
lemma angle_neg_zero_neg (v₁ v₃ : V) :
    ∠ (-v₁) (0 : V) (-v₃) = ∠ v₁ (0 : V) v₃ := by
  simpa using angle_neg v₁ (0 : V) v₃

/-- For points `T W X : Pt`, the unoriented angle
between vectors `W -ᵥ T` and `W -ᵥ X` (based at the origin of `V`) equals `∠ T W X`.

This allows angle computations stated in the affine setting (`Pt`) to be related
back to vector-space angle expressions (`V`). -/
lemma angle_vsub_vsub (T W X : Pt) :
    ∠ (W -ᵥ T) (0 : V) (W -ᵥ X) = ∠ T W X := by
  have h1 : W -ᵥ T = -(T -ᵥ W) := (neg_vsub_eq_vsub_rev T W).symm
  have h2 : W -ᵥ X = -(X -ᵥ W) := (neg_vsub_eq_vsub_rev X W).symm
  rw [h1, h2, angle_neg_zero_neg]
  simpa [vsub_self] using angle_vsub_const T W X W

/-! ### Corresponding angles for parallel lines (同位角) -/

/-- **Corresponding Angles Theorem** (oriented version, 同位角-有向角版本):

If `line[ℝ, u, x] ∥ line[ℝ, v, w]` where `u` is strictly between `t` and `v`
(so the line `tv` acts as a transversal), `x` is strictly between `t` and `w`, and `u`
is not on line `tx` (non-degeneracy), then the oriented corresponding angles are equal:
`∡ t u x = ∡ t v w`.

This formalises the fact that parallel lines cut by a transversal give equal
corresponding oriented angles. -/
theorem oangle_corresponding_of_parallel {A B C D E : Pt}
  (h_ABC : Sbtw ℝ A B C)
  (h_ADE : Sbtw ℝ A D E)
  (h_par : line[ℝ, B, D] ∥ line[ℝ, C, E])
  (h_not_col : B ∉ line[ℝ, A, D]) :
  ∡ A B D = ∡ A C E := by
  -- We apply `oangle_eq_of_parallel` with the mapping:
  --   (p₁, p₂, p₃) ↦ (t, u, x)  and  (p₄, p₅, p₆) ↦ (t, v, w).
  -- The required conditions are:
  --   (1) u ∉ line[ℝ, t, x]               ← h_not_col (given)
  --   (2) t ∈ line[ℝ, t, x]               ← trivial
  --   (3) w ∈ line[ℝ, t, x]               ← from Sbtw t x w
  --   (4) line[ℝ, t, u] ∥ line[ℝ, t, v]  ← same line (u between t and v)
  --   (5) line[ℝ, x, u] ∥ line[ℝ, w, v]  ← same as h_par up to symmetry
  apply oangle_eq_of_parallel (p₁ := A) (p₂ := B) (p₃ := D) (p₄ := A) (p₅ := C) (p₆ := E)
  · exact h_not_col
  · exact left_mem_affineSpan_pair ℝ A D
  · exact h_ADE.right_mem_affineSpan
  · have heq : line[ℝ, A, C] = line[ℝ, A, B] :=
      affineSpan_pair_eq_of_right_mem_of_ne h_ABC.right_mem_affineSpan h_ABC.left_ne_right.symm
    rw [heq]
  · rw [affineSpan_pair_comm (k := ℝ) (p₁ := D) (p₂ := B),
      affineSpan_pair_comm (k := ℝ) (p₁ := E) (p₂ := C)]
    exact h_par

/-- **Corresponding Angles Theorem** (unoriented version, 同位角):

If `line[ℝ, u, x] ∥ line[ℝ, v, w]` where `u` is strictly between `t` and `v`,
`x` is strictly between `t` and `w`, `u ∉ line[ℝ, t, x]` (non-degeneracy), and `v ≠ w`,
then the unoriented corresponding angles are equal: `∠ t u x = ∠ t v w`.

**Note on `v ≠ w`**: This holds whenever `u ≠ x` (which follows from `h_not_col`)
and `line[ℝ, u, x] ∥ line[ℝ, v, w]` — equal-direction lines must both be proper.
In practice, `v ≠ w` can be supplied directly from the problem hypotheses. -/
theorem angle_corresponding_of_parallel {A B C D E : Pt}
    (h_ABC : Sbtw ℝ A B C)
    (h_ADE : Sbtw ℝ A D E)
    (h_par : line[ℝ, B, D] ∥ line[ℝ, C, E])
    (h_not_col : B ∉ line[ℝ, A, D])
    (h_CE : C ≠ E) :
    ∠ A B D = ∠ A C E := by
  have h_oangle := oangle_corresponding_of_parallel h_ABC h_ADE h_par h_not_col
  have hAB : A ≠ B := h_ABC.left_ne
  have hDB : D ≠ B := fun h_eq =>
    h_not_col (h_eq ▸ right_mem_affineSpan_pair ℝ A D)
  have hAC : A ≠ C := h_ABC.left_ne_right
  rw [angle_eq_abs_oangle_toReal hAB hDB,
      angle_eq_abs_oangle_toReal hAC h_CE.symm,
      h_oangle]

/-! ### Ray invariance: replacing a point by another on the same ray -/

/-- **Ray invariance of unoriented angles** (同向射线):

If `Sbtw ℝ t u v` (so `u` lies strictly between `t` and `v`), then for any
`w : Pt` with `v ≠ w` and `v ≠ u`, the angles `∠ t v w = ∠ u v w`.

Geometrically: both `t` and `u` lie on the same ray from `v` (in the direction from
`v` toward `t`, which also passes through `u`). Hence any angle measured at `v`
toward `t` equals the angle toward `u`. -/
theorem angle_sbtw_left_eq {A B C D : Pt}
    (h : Sbtw ℝ A B C) (h_CD : C ≠ D) :
    ∠ A C D = ∠ B C D := by
  -- Step 1: SameRay ℝ (v -ᵥ t) (v -ᵥ u) from Wbtw
  have h_sr : SameRay ℝ (C -ᵥ A) (C -ᵥ B) := h.wbtw.sameRay_vsub_right
  -- Step 2: Convert to SameRay ℝ (t -ᵥ v) (u -ᵥ v) by negating
  have h_sr' : SameRay ℝ (A -ᵥ C) (B -ᵥ C) := by
    rwa [show A -ᵥ C = -(C -ᵥ A) from (neg_vsub_eq_vsub_rev C A).symm,
         show B -ᵥ C = -(C -ᵥ B) from (neg_vsub_eq_vsub_rev C B).symm,
         sameRay_neg_iff]
  -- Step 3: Both vectors are nonzero
  have hAC : A -ᵥ C ≠ 0 := vsub_ne_zero.2 h.left_ne_right
  have hBC : B -ᵥ C ≠ 0 := vsub_ne_zero.2 h.ne_right
  -- Step 4: Extract positive scalar r • (t -ᵥ v) = u -ᵥ v
  obtain ⟨r, hr, hrxy⟩ := (exists_pos_left_iff_sameRay hAC hBC).mpr h_sr'
  -- Step 5: Use angle_smul_left_of_pos
  -- ∠ t v w = InnerProductGeometry.angle (t -ᵥ v) (w -ᵥ v)
  -- ∠ u v w = InnerProductGeometry.angle (u -ᵥ v) (w -ᵥ v)
  --         = InnerProductGeometry.angle (r • (t -ᵥ v)) (w -ᵥ v)  [by hrxy.symm]
  --         = InnerProductGeometry.angle (t -ᵥ v) (w -ᵥ v)        [by angle_smul_left_of_pos]
  simp only [EuclideanGeometry.angle, ← hrxy,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hr]

/-! ### Alternate-interior and co-interior angle lemmas -/

/-- **Alternate-interior angles are equal** for a transversal cutting parallel lines.

If `line[ℝ, u, x] ∥ line[ℝ, v, w]` where `u` is strictly between `t` and `v`,
`x` is strictly between `t` and `w`, with `u ∉ line[ℝ, t, x]` (non-degeneracy)
and `v ≠ w`, then `∠ t u x = ∠ u v w`.

This is obtained by combining corresponding-angle equality with ray invariance on the
transversal. -/
theorem angle_alternate_interior_of_parallel {A B C D E : Pt}
    (h_ABC : Sbtw ℝ A B C)
    (h_ADE : Sbtw ℝ A D E)
    (h_par : line[ℝ, B, D] ∥ line[ℝ, C, E])
    (h_not_col : B ∉ line[ℝ, A, D])
    (h_CE : C ≠ E) :
    ∠ A B D = ∠ B C E := by
  have h1 : ∠ A B D = ∠ A C E :=
    angle_corresponding_of_parallel h_ABC h_ADE h_par h_not_col h_CE
  have h2 : ∠ A C E = ∠ B C E :=
    angle_sbtw_left_eq h_ABC h_CE
  exact h1.trans h2

/-- Compatibility wrapper for `angle_alternate_interior_of_parallel`. -/
theorem angle_parallel_transversal {A B C D E : Pt}
    (h_ABC : Sbtw ℝ A B C)
    (h_ADE : Sbtw ℝ A D E)
    (h_par : line[ℝ, B, D] ∥ line[ℝ, C, E])
    (h_not_col : B ∉ line[ℝ, A, D])
    (h_CE : C ≠ E) :
    ∠ A B D = ∠ B C E :=
  angle_alternate_interior_of_parallel h_ABC h_ADE h_par h_not_col h_CE

/-- **Co-interior angles are supplementary** in the same basic parallel-transversal setup. -/
theorem angle_cointerior_eq_pi_of_parallel {A B C D E : Pt}
    (h_ABC : Sbtw ℝ A B C)
    (h_ADE : Sbtw ℝ A D E)
    (h_par : line[ℝ, B, D] ∥ line[ℝ, C, E])
    (h_not_col : B ∉ line[ℝ, A, D])
    (h_CE : C ≠ E) :
    ∠ D B C + ∠ B C E = π := by
  have h_alt : ∠ A B D = ∠ B C E :=
    angle_alternate_interior_of_parallel h_ABC h_ADE h_par h_not_col h_CE
  have h_straight : ∠ A B D + ∠ D B C = π := by
    simpa [angle_comm] using angle_add_angle_eq_pi_of_angle_eq_pi D h_ABC.angle₁₂₃_eq_pi
  calc
    ∠ D B C + ∠ B C E = ∠ D B C + ∠ A B D := by rw [h_alt.symm]
    _ = π := by simpa [add_comm] using h_straight

/-- A 4-point co-interior-angle version: if `AB ∥ CD`, the transversal `AC` meets the two
parallel lines at `A` and `C`, and `B, D` lie on the same side of `AC`, then
`∠ B A C + ∠ A C D = π`. -/
theorem angle_cointerior_eq_pi_of_parallel_sameSide {A B C D : Pt}
    (h_AC : A ≠ C)
    (h_same : line[ℝ, A, C].SSameSide B D)
    (h_par : line[ℝ, A, B] ∥ line[ℝ, C, D]) :
    ∠ B A C + ∠ A C D = π := by
  have h_sign_base : (∡ C D A).sign = (∡ C B A).sign :=
    h_same.oangle_sign_eq (right_mem_affineSpan_pair ℝ A C) (left_mem_affineSpan_pair ℝ A C)
  have h_sign_same : (∡ A C D).sign = (∡ B A C).sign := by
    have h_left : (∡ A C D).sign = (∡ C D A).sign := by
      rw [oangle_rotate_sign D A C, oangle_rotate_sign C D A]
    have h_right : (∡ C B A).sign = (∡ B A C).sign := by
      rw [oangle_rotate_sign A C B, oangle_rotate_sign B A C]
    exact h_left.trans (h_sign_base.trans h_right)
  have h_BAC_sign_ne_zero : (∡ B A C).sign ≠ 0 := by
    intro h_zero
    have h_col : Collinear ℝ ({B, A, C} : Set Pt) :=
      (oangle_sign_eq_zero_iff_collinear : (∡ B A C).sign = 0 ↔ Collinear ℝ ({B, A, C} : Set Pt)).1
        h_zero
    have hB_mem_AC : B ∈ line[ℝ, A, C] :=
      h_col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_AC
    exact h_same.left_notMem hB_mem_AC
  obtain ⟨z, hz⟩ :=
    (affineSpan_pair_parallel_iff_exists_unit_smul (k := ℝ) (p₁ := A) (q₁ := B) (p₂ := C)
      (q₂ := D)).1 h_par
  have hz_pos : 0 < (z : ℝ) := by
    by_contra hz_not_pos
    have hz_nonpos : (z : ℝ) ≤ 0 := le_of_not_gt hz_not_pos
    have hz_neg : (z : ℝ) < 0 := lt_of_le_of_ne hz_nonpos (by simpa using z.ne_zero.symm)
    have h_oangle_eq : ∡ B A C = ∡ D C A := by
      rw [EuclideanGeometry.oangle, ← hz]
      change o.oangle ((z : ℝ) • (D -ᵥ C)) (C -ᵥ A) = ∡ D C A
      rw [o.oangle_smul_left_of_neg _ _ hz_neg, o.oangle_neg_left_eq_neg_right,
        neg_vsub_eq_vsub_rev]
      simp [EuclideanGeometry.oangle]
    have h_sign_neg : (∡ D C A).sign = - (∡ A C D).sign := by
      rw [oangle_rev, Real.Angle.sign_neg]
    have hnegself : - (∡ B A C).sign = (∡ B A C).sign := by
      calc
        - (∡ B A C).sign = - (∡ A C D).sign := by rw [h_sign_same]
        _ = (∡ D C A).sign := by rw [← h_sign_neg]
        _ = (∡ B A C).sign := by rw [h_oangle_eq]
    exact h_BAC_sign_ne_zero (SignType.neg_eq_self_iff.mp hnegself)
  have h_angle_left : ∠ B A C = InnerProductGeometry.angle (D -ᵥ C) (C -ᵥ A) := by
    rw [EuclideanGeometry.angle, ← hz]
    change InnerProductGeometry.angle ((z : ℝ) • (D -ᵥ C)) (C -ᵥ A) =
      InnerProductGeometry.angle (D -ᵥ C) (C -ᵥ A)
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hz_pos]
  have h_angle_right : ∠ A C D = π - InnerProductGeometry.angle (D -ᵥ C) (C -ᵥ A) := by
    rw [EuclideanGeometry.angle,
      show A -ᵥ C = -(C -ᵥ A) from (neg_vsub_eq_vsub_rev C A).symm,
      InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_comm]
  linarith [h_angle_left, h_angle_right]

/-- Converse to `angle_cointerior_eq_pi_of_parallel_sameSide`: in the same 4-point same-side
configuration, supplementary co-interior angles force parallel lines. -/
theorem parallel_of_angle_cointerior_eq_pi_sameSide {A B C D : Pt}
    (h_AC : A ≠ C)
    (h_same : line[ℝ, A, C].SSameSide B D)
    (h_angle : ∠ B A C + ∠ A C D = π) :
    line[ℝ, A, B] ∥ line[ℝ, C, D] := by
  let u := B -ᵥ A
  let v := C -ᵥ A
  let w := D -ᵥ C
  have hu : u ≠ 0 := by
    refine vsub_ne_zero.2 ?_
    intro hBA
    exact h_same.left_notMem (hBA ▸ left_mem_affineSpan_pair ℝ A C)
  have hv : v ≠ 0 := by
    exact vsub_ne_zero.2 h_AC.symm
  have hw : w ≠ 0 := by
    refine vsub_ne_zero.2 ?_
    intro hDC
    exact h_same.right_notMem (hDC ▸ right_mem_affineSpan_pair ℝ A C)
  have h_angle_left : ∠ u (0 : V) v = ∠ B A C := by
    simp [u, v, EuclideanGeometry.angle]
  have h_angle_right : ∠ v (0 : V) w = π - ∠ A C D := by
    have h_vec : ∠ v (0 : V) w = InnerProductGeometry.angle (C -ᵥ A) (D -ᵥ C) := by
      simp [EuclideanGeometry.angle, v, w]
    have h_pt : InnerProductGeometry.angle (C -ᵥ A) (D -ᵥ C) = π - ∠ A C D := by
      rw [EuclideanGeometry.angle,
        show A -ᵥ C = -(C -ᵥ A) from (neg_vsub_eq_vsub_rev C A).symm,
        InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_comm]
      linarith
    exact h_vec.trans h_pt
  have h_angle_vec : ∠ u (0 : V) v = ∠ v (0 : V) w := by
    linarith [h_angle, h_angle_left, h_angle_right]
  have h_sign_base : (∡ C D A).sign = (∡ C B A).sign :=
    h_same.oangle_sign_eq (right_mem_affineSpan_pair ℝ A C) (left_mem_affineSpan_pair ℝ A C)
  have h_sign_same : (∡ A C D).sign = (∡ B A C).sign := by
    have h_left : (∡ A C D).sign = (∡ C D A).sign := by
      rw [oangle_rotate_sign D A C, oangle_rotate_sign C D A]
    have h_right : (∡ C B A).sign = (∡ B A C).sign := by
      rw [oangle_rotate_sign A C B, oangle_rotate_sign B A C]
    exact h_left.trans (h_sign_base.trans h_right)
  have h_sign_left : (∡ u (0 : V) v).sign = (∡ B A C).sign := by
    simp [EuclideanGeometry.oangle, u, v]
  have h_sign_right : (∡ v (0 : V) w).sign = - (∡ A C D).sign := by
    calc
      (∡ v (0 : V) w).sign = (o.oangle (C -ᵥ A) (D -ᵥ C)).sign := by
        simp [EuclideanGeometry.oangle, v, w]
      _ = - (o.oangle (A -ᵥ C) (D -ᵥ C)).sign := by
        rw [show C -ᵥ A = -(A -ᵥ C) from (neg_vsub_eq_vsub_rev A C).symm,
          o.oangle_sign_neg_left]
      _ = - (∡ A C D).sign := by
        simp [EuclideanGeometry.oangle]
  have h_sign_neg_vec : (∡ u (0 : V) v).sign = - (∡ v (0 : V) w).sign := by
    rw [h_sign_left, h_sign_right, h_sign_same]
    simp
  have h_sign_left_ne_zero : (∡ u (0 : V) v).sign ≠ 0 := by
    rw [h_sign_left]
    intro h_zero
    have h_col : Collinear ℝ ({B, A, C} : Set Pt) :=
      (oangle_sign_eq_zero_iff_collinear : (∡ B A C).sign = 0 ↔ Collinear ℝ ({B, A, C} : Set Pt)).1
        h_zero
    have hB_mem_AC : B ∈ line[ℝ, A, C] :=
      h_col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_AC
    exact h_same.left_notMem hB_mem_AC
  have h_ray : SameRay ℝ u w := by
    rcases (angle_eq_iff_oangle_eq_or_wbtw (p₁ := u) (p₂ := (0 : V)) (p₃ := v) (p₄ := w) hu hw).1
        h_angle_vec with h_o | h_wbtw | h_wbtw
    · have h_same_sign : (∡ u (0 : V) v).sign = (∡ v (0 : V) w).sign := by
        simpa [h_o]
      have hnegself : - (∡ v (0 : V) w).sign = (∡ v (0 : V) w).sign := by
        simpa [h_same_sign] using h_sign_neg_vec.symm
      have hzero_right : (∡ v (0 : V) w).sign = 0 := SignType.neg_eq_self_iff.mp hnegself
      exact False.elim <| h_sign_left_ne_zero (by rw [h_same_sign, hzero_right])
    · simpa [u, w] using h_wbtw.sameRay_vsub_left
    · exact (by simpa [u, w] using h_wbtw.sameRay_vsub_left : SameRay ℝ w u).symm
  obtain ⟨r, hr, hr_eq⟩ := (exists_pos_left_iff_sameRay hw hu).2 h_ray.symm
  refine (affineSpan_pair_parallel_iff_exists_unit_smul (k := ℝ) (p₁ := A) (q₁ := B) (p₂ := C)
    (q₂ := D)).2 ?_
  refine ⟨Units.mk0 r hr.ne', ?_⟩
  simpa [u, w] using hr_eq

/-- Four-point same-side criterion: with transversal `AC`, the co-interior-angle condition is
equivalent to `AB ∥ CD`. -/
theorem parallel_iff_angle_cointerior_eq_pi_sameSide {A B C D : Pt}
    (h_AC : A ≠ C)
    (h_same : line[ℝ, A, C].SSameSide B D) :
    line[ℝ, A, B] ∥ line[ℝ, C, D] ↔ ∠ B A C + ∠ A C D = π := by
  constructor
  · intro h_par
    exact angle_cointerior_eq_pi_of_parallel_sameSide h_AC h_same h_par
  · intro h_angle
    exact parallel_of_angle_cointerior_eq_pi_sameSide h_AC h_same h_angle

/-! ### Parallelogram properties (平行四边形性质) -/

/-- **Parallelogram vector identity**:

If the vector `H -ᵥ G` equals the vector `J -ᵥ I` (i.e., `GH` and `IJ` represent the
same displacement), then the distances `dist H J = dist G I`.

Proof: From `H - G = J - I` we compute `J - H = I - G`, so
`dist H J = ‖J - H‖ = ‖I - G‖ = dist G I`.

**Use in UniGeo_Quadrilateral4**: When quadrilateral `GHJI` has `GH ∥ IJ` and
`GH = IJ` with co-oriented sides, this gives `dist H J = dist G I`. -/
theorem dist_of_parallelogram_vsub {A B C D : Pt}
    (h : B -ᵥ A = D -ᵥ C) : dist B D = dist A C := by
  have hDB : D -ᵥ B = C -ᵥ A :=
    calc D -ᵥ B = (D -ᵥ C) + (C -ᵥ B) := by rw [vsub_add_vsub_cancel]
    _ = (B -ᵥ A) + (C -ᵥ B) := by rw [← h]
    _ = C -ᵥ A := by rw [add_comm, vsub_add_vsub_cancel]
  have hBD : B -ᵥ D = A -ᵥ C := by
    simpa [neg_vsub_eq_vsub_rev] using congrArg Neg.neg hDB
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, hBD]

/-- Equal lengths together with co-oriented displacement vectors force the opposite connector
distances to agree. -/
theorem dist_of_eq_dist_of_sameRay_vsub {A B C D : Pt}
    (h_dist : dist A B = dist C D)
    (h_orient : SameRay ℝ (B -ᵥ A) (D -ᵥ C)) :
    dist B D = dist A C := by
  by_cases hAB : A = B
  · have hCD_eq : C = D := by
      exact dist_eq_zero.mp <| by simpa [hAB] using h_dist.symm
    simp [hAB, hCD_eq]
  · have hCD : C ≠ D := by
      intro hCD
      exact hAB <| dist_eq_zero.mp <| by simpa [hCD] using h_dist
    have hBA : B -ᵥ A ≠ 0 := by
      refine vsub_ne_zero.2 ?_
      intro h_eq
      exact hAB h_eq.symm
    have hDC : D -ᵥ C ≠ 0 := by
      refine vsub_ne_zero.2 ?_
      intro h_eq
      exact hCD h_eq.symm
    obtain ⟨r, hr, hrxy⟩ := (exists_pos_left_iff_sameRay hBA hDC).mpr h_orient
    have h_r_one : r = 1 := by
      have h_norm : ‖B -ᵥ A‖ = ‖D -ᵥ C‖ := by
        simpa [dist_eq_norm_vsub' V] using h_dist
      rw [← hrxy, norm_smul, Real.norm_of_nonneg hr.le] at h_norm
      have hmul : (r - 1) * ‖B -ᵥ A‖ = 0 := by nlinarith
      have hnorm_ne : ‖B -ᵥ A‖ ≠ 0 := norm_ne_zero_iff.2 hBA
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · linarith
      · exact False.elim (hnorm_ne hzero)
    rw [h_r_one, one_smul] at hrxy
    exact dist_of_parallelogram_vsub hrxy

/-- Equal lengths together with co-oriented displacement vectors force the opposite connector
distances to agree; no separate parallelism hypothesis is needed. -/
theorem dist_of_eq_dist_cooriented {A B C D : Pt}
    (h_dist : dist A B = dist C D)
    (h_orient : SameRay ℝ (B -ᵥ A) (D -ᵥ C)) :
    dist B D = dist A C := by
  exact dist_of_eq_dist_of_sameRay_vsub h_dist h_orient

/-- **One pair of parallel equal opposite sides → equal other sides** (平行四边形判定):

If `line[ℝ, G, H] ∥ line[ℝ, I, J]`, `dist G H = dist I J`, and the sides
`GH` and `IJ` are co-oriented (i.e., `H -ᵥ G` and `J -ᵥ I` are in the same
direction, captured by `SameRay ℝ (H -ᵥ G) (J -ᵥ I)`), then `dist H J = dist G I`.

The co-orientation condition distinguishes the *parallelogram* case
(`H -ᵥ G = J -ᵥ I`) from the *antiparallel* case (`H -ᵥ G = -(J -ᵥ I)`).
For a proper (non-crossing) quadrilateral with vertices in order, this holds
automatically. -/
theorem dist_of_parallel_eq_dist_cooriented {A B C D : Pt}
    (_h_par : line[ℝ, A, B] ∥ line[ℝ, C, D])
    (h_dist : dist A B = dist C D)
    (h_orient : SameRay ℝ (B -ᵥ A) (D -ᵥ C)) :
    dist B D = dist A C := by
  exact dist_of_eq_dist_cooriented h_dist h_orient

/-- Transport a `SSameSide` relation across a line equality. -/
theorem sSameSide_of_line_eq {A B P Q E F : Pt}
    (h_line : line[ℝ, P, Q] = line[ℝ, E, F])
    (h_same : line[ℝ, E, F].SSameSide A B) :
    line[ℝ, P, Q].SSameSide A B := by
  simpa [h_line] using h_same

/-- Transport a `SOppSide` relation across a line equality. -/
theorem sOppSide_of_line_eq {A B P Q E F : Pt}
    (h_line : line[ℝ, P, Q] = line[ℝ, E, F])
    (h_opp : line[ℝ, E, F].SOppSide A B) :
    line[ℝ, P, Q].SOppSide A B := by
  simpa [h_line] using h_opp

/-! ### Co-interior angles → parallel (同侧内角互补 → 平行) -/

/-- In a transversal configuration, parallel lines give equal corresponding angles. -/
theorem angle_corresponding_of_parallel_intersections {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B)
    (h_par : line[ℝ, C, D] ∥ line[ℝ, A, B]) :
    ∠ A P Q = ∠ C Q F := by
  have hP_mem_EF : P ∈ line[ℝ, E, F] := hP.2
  have hQ_mem_EF : Q ∈ line[ℝ, E, F] := hQ.2
  have hA_not_mem_EF : A ∉ line[ℝ, E, F] := h_CA.right_notMem
  have hA_opposite_B : line[ℝ, E, F].SOppSide A B :=
    h_APB.sOppSide_of_notMem_of_mem hA_not_mem_EF hP_mem_EF
  have hA_opposite_D : line[ℝ, E, F].SOppSide A D :=
    hA_opposite_B.trans_sSameSide h_DB.symm
  have h_sign_neg_QAP : (∡ Q D P).sign = -(∡ Q A P).sign :=
    hA_opposite_D.oangle_sign_eq_neg hQ_mem_EF hP_mem_EF
  have h_sign_neg : (∡ P Q D).sign = -(∡ A P Q).sign := by
    have h_rot_QDP : (∡ P Q D).sign = (∡ Q D P).sign := by
      rw [oangle_rotate_sign D P Q, oangle_rotate_sign Q D P]
    have h_rot_QAP : (∡ Q A P).sign = (∡ A P Q).sign := by
      rw [← oangle_rotate_sign Q A P, ← oangle_rotate_sign A P Q]
    calc (∡ P Q D).sign = (∡ Q D P).sign := h_rot_QDP
      _ = -(∡ Q A P).sign := h_sign_neg_QAP
      _ = -(∡ A P Q).sign := by rw [h_rot_QAP]
  have h_PQ_ne : P ≠ Q := h_EPQ.ne_right
  have h_line_AP_eq_AB : line[ℝ, A, P] = line[ℝ, A, B] :=
    affineSpan_pair_eq_of_right_mem_of_ne hP.1 h_APB.left_ne.symm
  have h_line_QD_eq_CD : line[ℝ, Q, D] = line[ℝ, C, D] :=
    affineSpan_pair_eq_of_left_mem_of_ne hQ.1 h_CQD.right_ne.symm
  have h_parallel_AP_QD : line[ℝ, A, P] ∥ line[ℝ, Q, D] := by
    simpa [h_line_AP_eq_AB, h_line_QD_eq_CD] using h_par.symm
  have h_two : (2 : ℤ) • ∡ A P Q = (2 : ℤ) • ∡ D Q P := by
    apply two_zsmul_oangle_of_parallel
    · simpa [affineSpan_pair_comm (k := ℝ) (p₁ := D) (p₂ := Q)] using h_parallel_AP_QD
    · rw [affineSpan_pair_comm (k := ℝ) (p₁ := P) (p₂ := Q)]
  have h_APQ_sign_ne_zero : (∡ A P Q).sign ≠ 0 := by
    intro h_zero
    have h_line_PQ_eq_EF : line[ℝ, P, Q] = line[ℝ, E, F] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hP_mem_EF hQ_mem_EF h_PQ_ne
    have h_col : Collinear ℝ ({A, P, Q} : Set Pt) :=
      (oangle_sign_eq_zero_iff_collinear : (∡ A P Q).sign = 0 ↔ Collinear ℝ ({A, P, Q} : Set Pt)).1
        h_zero
    have hA_mem_PQ : A ∈ line[ℝ, P, Q] :=
      h_col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_PQ_ne
    exact hA_not_mem_EF <| h_line_PQ_eq_EF ▸ hA_mem_PQ
  have h_sign_alt : (∡ A P Q).sign = (∡ D Q P).sign := by
    calc
      (∡ A P Q).sign = -((∡ P Q D).sign) := by simpa [h_sign_neg]
      _ = (∡ D Q P).sign := by simpa using oangle_swap₁₃_sign P Q D
  have h_oangle : ∡ A P Q = ∡ D Q P := by
    exact (Real.Angle.two_zsmul_eq_iff_eq h_APQ_sign_ne_zero h_sign_alt).1 h_two
  have h_alt : ∠ A P Q = ∠ D Q P :=
    (angle_eq_iff_oangle_eq_of_sign_eq h_APB.left_ne h_EPQ.ne_right.symm
      h_CQD.right_ne h_EPQ.ne_right h_sign_alt).2 h_oangle
  have h_CQD_pi : ∠ C Q D = π := h_CQD.angle₁₂₃_eq_pi
  have h_FQP_pi : ∠ F Q P = π := h_PQF.symm.angle₁₂₃_eq_pi
  have h_CQF_eq_DQP : ∠ C Q F = ∠ D Q P := by
    simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_CQD_pi h_FQP_pi
  exact h_alt.trans h_CQF_eq_DQP.symm

/-- In a transversal configuration, parallel lines give equal alternate-interior angles. -/
theorem angle_alternate_interior_of_parallel_intersections {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B)
    (h_par : line[ℝ, C, D] ∥ line[ℝ, A, B]) :
    ∠ A P Q = ∠ D Q P := by
  have h_corr : ∠ A P Q = ∠ C Q F :=
    angle_corresponding_of_parallel_intersections hP h_APB h_PQF hQ h_CQD h_EPQ h_CA h_DB h_par
  have h_CQD_pi : ∠ C Q D = π := h_CQD.angle₁₂₃_eq_pi
  have h_FQP_pi : ∠ F Q P = π := h_PQF.symm.angle₁₂₃_eq_pi
  have h_CQF_eq_DQP : ∠ C Q F = ∠ D Q P := by
    simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_CQD_pi h_FQP_pi
  exact h_corr.trans h_CQF_eq_DQP

/-- In a transversal configuration, parallel lines make the same-side interior angles supplementary. -/
theorem angle_cointerior_eq_pi_of_parallel_intersections {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B)
    (h_par : line[ℝ, C, D] ∥ line[ℝ, A, B]) :
    ∠ E P A + ∠ C Q F = π := by
  have h_EPA_add_APQ : ∠ E P A + ∠ A P Q = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi A h_EPQ.angle₁₂₃_eq_pi
  have h_corr : ∠ A P Q = ∠ C Q F :=
    angle_corresponding_of_parallel_intersections hP h_APB h_PQF hQ h_CQD h_EPQ h_CA h_DB h_par
  linarith

/-- If two angles are supplementary to the same angle, then they are equal. -/
theorem eq_of_add_eq_pi_left {x y z : ℝ}
    (hxy : x + y = π) (hxz : x + z = π) : y = z := by
  linarith

/-- In the intersection-transversal setup, `∠EPA + ∠CQF = π` implies `∠APQ = ∠CQF`. -/
theorem angle_APQ_eq_CQF_of_cointerior_sum {A C E F P Q : Pt}
    (h_EPQ : Sbtw ℝ E P Q)
    (angle_sum : ∠ E P A + ∠ C Q F = π) :
    ∠ A P Q = ∠ C Q F := by
  have h_EPA_add_APQ : ∠ E P A + ∠ A P Q = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi A h_EPQ.angle₁₂₃_eq_pi
  exact (eq_of_add_eq_pi_left angle_sum h_EPA_add_APQ).symm

/-- In the intersection-transversal setup, `∠APQ = ∠CQF` implies
`∠EPA + ∠CQF = π`. -/
theorem angle_cointerior_sum_of_APQ_eq_CQF {A C E F P Q : Pt}
    (h_EPQ : Sbtw ℝ E P Q)
    (h_eq : ∠ A P Q = ∠ C Q F) :
    ∠ E P A + ∠ C Q F = π := by
  have h_EPA_add_APQ : ∠ E P A + ∠ A P Q = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi A h_EPQ.angle₁₂₃_eq_pi
  linarith

/-- Convert the co-interior-angle condition from the `(E,P,A)` / `(C,Q,F)` form to the
four-point `(A,P,Q)` / `(P,Q,C)` form used by `parallel_of_angle_cointerior_eq_pi_sameSide`. -/
theorem angle_cointerior_transfer_to_PQ {A C E F P Q : Pt}
    (h_PQF : Sbtw ℝ P Q F)
    (h_EPQ : Sbtw ℝ E P Q)
    (angle_sum : ∠ E P A + ∠ C Q F = π) :
    ∠ A P Q + ∠ P Q C = π := by
  have h_APQ_eq_CQF : ∠ A P Q = ∠ C Q F :=
    angle_APQ_eq_CQF_of_cointerior_sum h_EPQ angle_sum
  have h_PQC_add_CQF : ∠ P Q C + ∠ C Q F = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi C h_PQF.angle₁₂₃_eq_pi
  linarith [h_APQ_eq_CQF, h_PQC_add_CQF]

/-- **Co-interior Angles imply Parallel Lines** (同侧内角互补 → 两直线平行):

If two lines `line[ℝ, S, U]` and `line[ℝ, V, X]` are cut by transversal `line[ℝ, R, Y]`
at `T` and `W` respectively, with the betweenness conditions encoding proper crossings,
and if the co-interior (same-side interior) angles sum to `π`:
`∠ R T S + ∠ V₁ W Y = π`, then `line[ℝ, V₁, X] ∥ line[ℝ, S, U]`.

This is the "co-interior angles → parallel" theorem (同侧内角互补则两直线平行),
one of the fundamental results of Chinese high-school parallel-line theory. -/
theorem parallel_of_cointerior_angles {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B)
    (angle_sum : ∠ E P A + ∠ C Q F = π) :
  line[ℝ, C, D] ∥ line[ℝ, A, B] := by
  have h_APQ_add_PQC : ∠ A P Q + ∠ P Q C = π :=
    angle_cointerior_transfer_to_PQ h_PQF h_EPQ angle_sum
  have hP_mem_EF : P ∈ line[ℝ, E, F] := hP.2
  have hQ_mem_EF : Q ∈ line[ℝ, E, F] := hQ.2
  have h_PQ_ne : P ≠ Q := h_EPQ.ne_right
  have h_line_PQ_eq_EF : line[ℝ, P, Q] = line[ℝ, E, F] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hP_mem_EF hQ_mem_EF h_PQ_ne
  have h_same_AC : line[ℝ, P, Q].SSameSide A C := by
    exact sSameSide_of_line_eq h_line_PQ_eq_EF h_CA.symm
  have h_par_PA_QC : line[ℝ, P, A] ∥ line[ℝ, Q, C] :=
    parallel_of_angle_cointerior_eq_pi_sameSide h_PQ_ne h_same_AC h_APQ_add_PQC
  have h_line_AP_eq_AB : line[ℝ, A, P] = line[ℝ, A, B] :=
    affineSpan_pair_eq_of_right_mem_of_ne hP.1 h_APB.left_ne.symm
  have h_line_PA_eq_AB : line[ℝ, P, A] = line[ℝ, A, B] := by
    simpa [affineSpan_pair_comm (k := ℝ) (p₁ := P) (p₂ := A)] using h_line_AP_eq_AB
  have h_line_CQ_eq_CD : line[ℝ, C, Q] = line[ℝ, C, D] :=
    affineSpan_pair_eq_of_right_mem_of_ne hQ.1 h_CQD.left_ne.symm
  have h_line_QC_eq_CD : line[ℝ, Q, C] = line[ℝ, C, D] := by
    simpa [affineSpan_pair_comm (k := ℝ) (p₁ := Q) (p₂ := C)] using h_line_CQ_eq_CD
  have h_par_AB_CD : line[ℝ, A, B] ∥ line[ℝ, C, D] := by
    simpa [h_line_PA_eq_AB, h_line_QC_eq_CD] using h_par_PA_QC
  exact h_par_AB_CD.symm

/-- In the standard transversal configuration, parallelism is equivalent to equality of the
corresponding interior angles. -/
theorem parallel_iff_angle_corresponding_eq {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B) :
    line[ℝ, C, D] ∥ line[ℝ, A, B] ↔ ∠ A P Q = ∠ C Q F := by
  constructor
  · intro h_par
    exact angle_corresponding_of_parallel_intersections hP h_APB h_PQF hQ h_CQD h_EPQ h_CA h_DB h_par
  · intro h_eq
    apply parallel_of_cointerior_angles hP h_APB h_PQF hQ h_CQD h_EPQ h_CA h_DB
    exact angle_cointerior_sum_of_APQ_eq_CQF h_EPQ h_eq

/-- In the standard transversal configuration, parallelism is equivalent to equality of the
alternate-interior angles. -/
theorem parallel_iff_angle_alternate_interior_eq {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B) :
    line[ℝ, C, D] ∥ line[ℝ, A, B] ↔ ∠ A P Q = ∠ D Q P := by
  constructor
  · intro h_par
    exact angle_alternate_interior_of_parallel_intersections hP h_APB h_PQF hQ
      h_CQD h_EPQ h_CA h_DB h_par
  · intro h_eq
    have h_CQD_pi : ∠ C Q D = π := h_CQD.angle₁₂₃_eq_pi
    have h_FQP_pi : ∠ F Q P = π := h_PQF.symm.angle₁₂₃_eq_pi
    have h_CQF_eq_DQP : ∠ C Q F = ∠ D Q P := by
      simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_CQD_pi h_FQP_pi
    apply parallel_of_cointerior_angles hP h_APB h_PQF hQ h_CQD h_EPQ h_CA h_DB
    exact angle_cointerior_sum_of_APQ_eq_CQF h_EPQ (h_eq.trans h_CQF_eq_DQP.symm)

/-- In the standard transversal configuration, parallelism is equivalent to the same-side
interior angles being supplementary. -/
theorem parallel_iff_angle_cointerior_eq_pi {A B C D E F P Q : Pt}
    (hP : P ∈ line[ℝ, A, B] ⊓ line[ℝ, E, F])
    (h_APB : Sbtw ℝ A P B)
    (h_PQF : Sbtw ℝ P Q F)
    (hQ : Q ∈ line[ℝ, C, D] ⊓ line[ℝ, E, F])
    (h_CQD : Sbtw ℝ C Q D)
    (h_EPQ : Sbtw ℝ E P Q)
    (h_CA : line[ℝ, E, F].SSameSide C A)
    (h_DB : line[ℝ, E, F].SSameSide D B) :
    line[ℝ, C, D] ∥ line[ℝ, A, B] ↔ ∠ E P A + ∠ C Q F = π := by
  constructor
  · intro h_par
    exact angle_cointerior_eq_pi_of_parallel_intersections hP h_APB h_PQF hQ
      h_CQD h_EPQ h_CA h_DB h_par
  · intro h_angle
    exact parallel_of_cointerior_angles hP h_APB h_PQF hQ h_CQD h_EPQ h_CA h_DB h_angle

end EuclideanGeometry
