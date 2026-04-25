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
theorem oangle_corresponding_of_parallel {t u v x w : Pt}
    (h_tuv : Sbtw ℝ t u v)
    (h_txw : Sbtw ℝ t x w)
    (h_par : line[ℝ, u, x] ∥ line[ℝ, v, w])
    (h_not_col : u ∉ line[ℝ, t, x]) :
    ∡ t u x = ∡ t v w := by
  -- We apply `oangle_eq_of_parallel` with the mapping:
  --   (p₁, p₂, p₃) ↦ (t, u, x)  and  (p₄, p₅, p₆) ↦ (t, v, w).
  -- The required conditions are:
  --   (1) u ∉ line[ℝ, t, x]               ← h_not_col (given)
  --   (2) t ∈ line[ℝ, t, x]               ← trivial
  --   (3) w ∈ line[ℝ, t, x]               ← from Sbtw t x w
  --   (4) line[ℝ, t, u] ∥ line[ℝ, t, v]  ← same line (u between t and v)
  --   (5) line[ℝ, x, u] ∥ line[ℝ, w, v]  ← same as h_par up to symmetry
  apply oangle_eq_of_parallel (p₁ := t) (p₂ := u) (p₃ := x) (p₄ := t) (p₅ := v) (p₆ := w)
  · exact h_not_col
  · exact left_mem_affineSpan_pair ℝ t x
  · -- w ∈ line[ℝ, t, x] because Sbtw ℝ t x w gives x ∈ line[ℝ, t, w], hence w ∈ line[ℝ, t, x]
    exact h_txw.right_mem_affineSpan
  · -- line[ℝ, t, u] = line[ℝ, t, v] because Sbtw ℝ t u v places v on line[ℝ, t, u]
    have heq : line[ℝ, t, v] = line[ℝ, t, u] :=
      affineSpan_pair_eq_of_right_mem_of_ne h_tuv.right_mem_affineSpan h_tuv.left_ne_right.symm
    rw [heq]
  · -- line[ℝ, x, u] ∥ line[ℝ, w, v]: rewrite using affineSpan_pair_comm and h_par.symm
    rw [affineSpan_pair_comm (k := ℝ) (p₁ := x) (p₂ := u),
      affineSpan_pair_comm (k := ℝ) (p₁ := w) (p₂ := v)]
    exact h_par

/-- **Corresponding Angles Theorem** (unoriented version, 同位角):

If `line[ℝ, u, x] ∥ line[ℝ, v, w]` where `u` is strictly between `t` and `v`,
`x` is strictly between `t` and `w`, `u ∉ line[ℝ, t, x]` (non-degeneracy), and `v ≠ w`,
then the unoriented corresponding angles are equal: `∠ t u x = ∠ t v w`.

**Note on `v ≠ w`**: This holds whenever `u ≠ x` (which follows from `h_not_col`)
and `line[ℝ, u, x] ∥ line[ℝ, v, w]` — equal-direction lines must both be proper.
In practice, `v ≠ w` can be supplied directly from the problem hypotheses. -/
theorem angle_corresponding_of_parallel {t u v x w : Pt}
    (h_tuv : Sbtw ℝ t u v)
    (h_txw : Sbtw ℝ t x w)
    (h_par : line[ℝ, u, x] ∥ line[ℝ, v, w])
    (h_not_col : u ∉ line[ℝ, t, x])
    (h_vw : v ≠ w) :
    ∠ t u x = ∠ t v w := by
  have h_oangle := oangle_corresponding_of_parallel h_tuv h_txw h_par h_not_col
  have ht_ne_u : t ≠ u := h_tuv.left_ne
  have hx_ne_u : x ≠ u := fun heq =>
    h_not_col (heq ▸ right_mem_affineSpan_pair ℝ t x)
  have ht_ne_v : t ≠ v := h_tuv.left_ne_right
  rw [angle_eq_abs_oangle_toReal ht_ne_u hx_ne_u,
      angle_eq_abs_oangle_toReal ht_ne_v h_vw.symm,
      h_oangle]

/-! ### Ray invariance: replacing a point by another on the same ray -/

/-- **Ray invariance of unoriented angles** (同向射线):

If `Sbtw ℝ t u v` (so `u` lies strictly between `t` and `v`), then for any
`w : Pt` with `v ≠ w` and `v ≠ u`, the angles `∠ t v w = ∠ u v w`.

Geometrically: both `t` and `u` lie on the same ray from `v` (in the direction from
`v` toward `t`, which also passes through `u`). Hence any angle measured at `v`
toward `t` equals the angle toward `u`. -/
theorem angle_sbtw_left_eq {t u v w : Pt}
    (h : Sbtw ℝ t u v) (h_vw : v ≠ w) (h_vu : v ≠ u) :
    ∠ t v w = ∠ u v w := by
  -- Step 1: SameRay ℝ (v -ᵥ t) (v -ᵥ u) from Wbtw
  have h_sr : SameRay ℝ (v -ᵥ t) (v -ᵥ u) := h.wbtw.sameRay_vsub_right
  -- Step 2: Convert to SameRay ℝ (t -ᵥ v) (u -ᵥ v) by negating
  have h_sr' : SameRay ℝ (t -ᵥ v) (u -ᵥ v) := by
    rwa [show t -ᵥ v = -(v -ᵥ t) from (neg_vsub_eq_vsub_rev v t).symm,
         show u -ᵥ v = -(v -ᵥ u) from (neg_vsub_eq_vsub_rev v u).symm,
         sameRay_neg_iff]
  -- Step 3: Both vectors are nonzero
  have h_tv : t -ᵥ v ≠ 0 := vsub_ne_zero.2 h.left_ne_right
  have h_uv : u -ᵥ v ≠ 0 := vsub_ne_zero.2 h_vu.symm
  -- Step 4: Extract positive scalar r • (t -ᵥ v) = u -ᵥ v
  obtain ⟨r, hr, hrxy⟩ := (exists_pos_left_iff_sameRay h_tv h_uv).mpr h_sr'
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
theorem angle_alternate_interior_of_parallel {t u v x w : Pt}
    (h_tuv : Sbtw ℝ t u v)
    (h_txw : Sbtw ℝ t x w)
    (h_par : line[ℝ, u, x] ∥ line[ℝ, v, w])
    (h_not_col : u ∉ line[ℝ, t, x])
    (h_vw : v ≠ w) :
    ∠ t u x = ∠ u v w := by
  have h1 : ∠ t u x = ∠ t v w :=
    angle_corresponding_of_parallel h_tuv h_txw h_par h_not_col h_vw
  have h2 : ∠ t v w = ∠ u v w :=
    angle_sbtw_left_eq h_tuv h_vw h_tuv.ne_right.symm
  exact h1.trans h2

/-- Compatibility wrapper for `angle_alternate_interior_of_parallel`. -/
theorem angle_parallel_transversal {t u v x w : Pt}
    (h_tuv : Sbtw ℝ t u v)
    (h_txw : Sbtw ℝ t x w)
    (h_par : line[ℝ, u, x] ∥ line[ℝ, v, w])
    (h_not_col : u ∉ line[ℝ, t, x])
    (h_vw : v ≠ w) :
    ∠ t u x = ∠ u v w :=
  angle_alternate_interior_of_parallel h_tuv h_txw h_par h_not_col h_vw

/-- **Co-interior angles are supplementary** in the same basic parallel-transversal setup. -/
theorem angle_cointerior_eq_pi_of_parallel {t u v x w : Pt}
    (h_tuv : Sbtw ℝ t u v)
    (h_txw : Sbtw ℝ t x w)
    (h_par : line[ℝ, u, x] ∥ line[ℝ, v, w])
    (h_not_col : u ∉ line[ℝ, t, x])
    (h_vw : v ≠ w) :
    ∠ x u v + ∠ u v w = π := by
  have h_alt : ∠ t u x = ∠ u v w :=
    angle_alternate_interior_of_parallel h_tuv h_txw h_par h_not_col h_vw
  have h_straight : ∠ t u x + ∠ x u v = π := by
    simpa [angle_comm] using angle_add_angle_eq_pi_of_angle_eq_pi x h_tuv.angle₁₂₃_eq_pi
  calc
    ∠ x u v + ∠ u v w = ∠ x u v + ∠ t u x := by rw [h_alt.symm]
    _ = π := by simpa [add_comm] using h_straight

/-! ### Parallelogram properties (平行四边形性质) -/

/-- **Parallelogram vector identity**:

If the vector `H -ᵥ G` equals the vector `J -ᵥ I` (i.e., `GH` and `IJ` represent the
same displacement), then the distances `dist H J = dist G I`.

Proof: From `H - G = J - I` we compute `J - H = I - G`, so
`dist H J = ‖J - H‖ = ‖I - G‖ = dist G I`.

**Use in UniGeo_Quadrilateral4**: When quadrilateral `GHJI` has `GH ∥ IJ` and
`GH = IJ` with co-oriented sides, this gives `dist H J = dist G I`. -/
theorem dist_of_parallelogram_vsub {G H I J : Pt}
    (h : H -ᵥ G = J -ᵥ I) : dist H J = dist G I := by
  have hJH : J -ᵥ H = I -ᵥ G :=
    calc J -ᵥ H = (J -ᵥ I) + (I -ᵥ H) := by rw [vsub_add_vsub_cancel]
    _ = (H -ᵥ G) + (I -ᵥ H) := by rw [← h]
    _ = I -ᵥ G := by rw [add_comm, vsub_add_vsub_cancel]
  have hHJ : H -ᵥ J = G -ᵥ I := by
    simpa [neg_vsub_eq_vsub_rev] using congrArg Neg.neg hJH
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, hHJ]

/-- Equal lengths together with co-oriented displacement vectors force the opposite connector
distances to agree. -/
theorem dist_of_eq_dist_of_sameRay_vsub {G H I J : Pt}
    (h_dist : dist G H = dist I J)
    (h_orient : SameRay ℝ (H -ᵥ G) (J -ᵥ I)) :
    dist H J = dist G I := by
  by_cases hGH : G = H
  · have hIJ : I = J := by
      exact dist_eq_zero.mp <| by simpa [hGH] using h_dist.symm
    simp [hGH, hIJ]
  · have hIJ : I ≠ J := by
      intro hIJ
      exact hGH <| dist_eq_zero.mp <| by simpa [hIJ] using h_dist
    have hHG : H -ᵥ G ≠ 0 := by
      refine vsub_ne_zero.2 ?_
      intro h_eq
      exact hGH h_eq.symm
    have hJI : J -ᵥ I ≠ 0 := by
      refine vsub_ne_zero.2 ?_
      intro h_eq
      exact hIJ h_eq.symm
    obtain ⟨r, hr, hrxy⟩ := (exists_pos_left_iff_sameRay hHG hJI).mpr h_orient
    have h_r_one : r = 1 := by
      have h_norm : ‖H -ᵥ G‖ = ‖J -ᵥ I‖ := by
        simpa [dist_eq_norm_vsub' V] using h_dist
      rw [← hrxy, norm_smul, Real.norm_of_nonneg hr.le] at h_norm
      have hmul : (r - 1) * ‖H -ᵥ G‖ = 0 := by nlinarith
      have hnorm_ne : ‖H -ᵥ G‖ ≠ 0 := norm_ne_zero_iff.2 hHG
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · linarith
      · exact False.elim (hnorm_ne hzero)
    rw [h_r_one, one_smul] at hrxy
    exact dist_of_parallelogram_vsub hrxy

/-- **One pair of parallel equal opposite sides → equal other sides** (平行四边形判定):

If `line[ℝ, G, H] ∥ line[ℝ, I, J]`, `dist G H = dist I J`, and the sides
`GH` and `IJ` are co-oriented (i.e., `H -ᵥ G` and `J -ᵥ I` are in the same
direction, captured by `SameRay ℝ (H -ᵥ G) (J -ᵥ I)`), then `dist H J = dist G I`.

The co-orientation condition distinguishes the *parallelogram* case
(`H -ᵥ G = J -ᵥ I`) from the *antiparallel* case (`H -ᵥ G = -(J -ᵥ I)`).
For a proper (non-crossing) quadrilateral with vertices in order, this holds
automatically. -/
theorem dist_of_parallel_eq_dist_cooriented {G H I J : Pt}
    (h_par : line[ℝ, G, H] ∥ line[ℝ, I, J])
    (h_dist : dist G H = dist I J)
    (h_orient : SameRay ℝ (H -ᵥ G) (J -ᵥ I)) :
    dist H J = dist G I := by
  let _ := h_par
  exact dist_of_eq_dist_of_sameRay_vsub h_dist h_orient

/-! ### Co-interior angles → parallel (同侧内角互补 → 平行) -/

/-- In a transversal configuration, parallel lines give equal corresponding angles. -/
theorem angle_corresponding_of_parallel_intersections {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U)
    (h_par : line[ℝ, V₁, X] ∥ line[ℝ, S, U]) :
    ∠ S T W = ∠ V₁ W Y := by
  have hT_mem_RY : T ∈ line[ℝ, R, Y] := T_def.2
  have hW_mem_RY : W ∈ line[ℝ, R, Y] := W_def.2
  have hS_not_mem_RY : S ∉ line[ℝ, R, Y] := V_SameSide_RY_S.right_notMem
  have hS_opposite_U : line[ℝ, R, Y].SOppSide S U :=
    Sbtw_STU.sOppSide_of_notMem_of_mem hS_not_mem_RY hT_mem_RY
  have hS_opposite_X : line[ℝ, R, Y].SOppSide S X :=
    hS_opposite_U.trans_sSameSide X_SameSide_RY_U.symm
  have h_sign_neg_WST : (∡ W X T).sign = -(∡ W S T).sign :=
    hS_opposite_X.oangle_sign_eq_neg hW_mem_RY hT_mem_RY
  have h_sign_neg : (∡ T W X).sign = -(∡ S T W).sign := by
    have h_rot_WXT : (∡ T W X).sign = (∡ W X T).sign := by
      rw [oangle_rotate_sign X T W, oangle_rotate_sign W X T]
    have h_rot_WST : (∡ W S T).sign = (∡ S T W).sign := by
      rw [← oangle_rotate_sign W S T, ← oangle_rotate_sign S T W]
    calc (∡ T W X).sign = (∡ W X T).sign := h_rot_WXT
      _ = -(∡ W S T).sign := h_sign_neg_WST
      _ = -(∡ S T W).sign := by rw [h_rot_WST]
  have h_TW_ne : T ≠ W := Sbtw_RTW.ne_right
  have h_line_ST_eq_SU : line[ℝ, S, T] = line[ℝ, S, U] :=
    affineSpan_pair_eq_of_right_mem_of_ne T_def.1 Sbtw_STU.left_ne.symm
  have h_line_WX_eq_VX : line[ℝ, W, X] = line[ℝ, V₁, X] :=
    affineSpan_pair_eq_of_left_mem_of_ne W_def.1 Sbtw_VWX.right_ne.symm
  have h_parallel_ST_WX : line[ℝ, S, T] ∥ line[ℝ, W, X] := by
    simpa [h_line_ST_eq_SU, h_line_WX_eq_VX] using h_par.symm
  have h_two : (2 : ℤ) • ∡ S T W = (2 : ℤ) • ∡ X W T := by
    apply two_zsmul_oangle_of_parallel
    · simpa [affineSpan_pair_comm (k := ℝ) (p₁ := X) (p₂ := W)] using h_parallel_ST_WX
    · rw [affineSpan_pair_comm (k := ℝ) (p₁ := T) (p₂ := W)]
  have h_STW_sign_ne_zero : (∡ S T W).sign ≠ 0 := by
    intro h_zero
    have h_line_TW_eq_RY : line[ℝ, T, W] = line[ℝ, R, Y] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hT_mem_RY hW_mem_RY h_TW_ne
    have h_col : Collinear ℝ ({S, T, W} : Set Pt) :=
      (oangle_sign_eq_zero_iff_collinear : (∡ S T W).sign = 0 ↔ Collinear ℝ ({S, T, W} : Set Pt)).1
        h_zero
    have hS_mem_TW : S ∈ line[ℝ, T, W] :=
      h_col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_TW_ne
    exact hS_not_mem_RY <| h_line_TW_eq_RY ▸ hS_mem_TW
  have h_sign_alt : (∡ S T W).sign = (∡ X W T).sign := by
    calc
      (∡ S T W).sign = -((∡ T W X).sign) := by simpa [h_sign_neg]
      _ = (∡ X W T).sign := by simpa using oangle_swap₁₃_sign T W X
  have h_oangle : ∡ S T W = ∡ X W T := by
    exact (Real.Angle.two_zsmul_eq_iff_eq h_STW_sign_ne_zero h_sign_alt).1 h_two
  have h_alt : ∠ S T W = ∠ X W T :=
    (angle_eq_iff_oangle_eq_of_sign_eq Sbtw_STU.left_ne Sbtw_RTW.ne_right.symm
      Sbtw_VWX.right_ne Sbtw_RTW.ne_right h_sign_alt).2 h_oangle
  have h_VWX_pi : ∠ V₁ W X = π := Sbtw_VWX.angle₁₂₃_eq_pi
  have h_YWT_pi : ∠ Y W T = π := Sbtw_TWY.symm.angle₁₂₃_eq_pi
  have h_VWY_eq_XWT : ∠ V₁ W Y = ∠ X W T := by
    simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_VWX_pi h_YWT_pi
  exact h_alt.trans h_VWY_eq_XWT.symm

/-- In a transversal configuration, parallel lines give equal alternate-interior angles. -/
theorem angle_alternate_interior_of_parallel_intersections {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U)
    (h_par : line[ℝ, V₁, X] ∥ line[ℝ, S, U]) :
    ∠ S T W = ∠ X W T := by
  have h_corr : ∠ S T W = ∠ V₁ W Y :=
    angle_corresponding_of_parallel_intersections T_def Sbtw_STU Sbtw_TWY W_def Sbtw_VWX
      Sbtw_RTW V_SameSide_RY_S X_SameSide_RY_U h_par
  have h_VWX_pi : ∠ V₁ W X = π := Sbtw_VWX.angle₁₂₃_eq_pi
  have h_YWT_pi : ∠ Y W T = π := Sbtw_TWY.symm.angle₁₂₃_eq_pi
  have h_VWY_eq_XWT : ∠ V₁ W Y = ∠ X W T := by
    simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_VWX_pi h_YWT_pi
  exact h_corr.trans h_VWY_eq_XWT

/-- In a transversal configuration, parallel lines make the same-side interior angles supplementary. -/
theorem angle_cointerior_eq_pi_of_parallel_intersections {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U)
    (h_par : line[ℝ, V₁, X] ∥ line[ℝ, S, U]) :
    ∠ R T S + ∠ V₁ W Y = π := by
  have h_RTS_add_STW : ∠ R T S + ∠ S T W = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi S Sbtw_RTW.angle₁₂₃_eq_pi
  have h_corr : ∠ S T W = ∠ V₁ W Y :=
    angle_corresponding_of_parallel_intersections T_def Sbtw_STU Sbtw_TWY W_def Sbtw_VWX
      Sbtw_RTW V_SameSide_RY_S X_SameSide_RY_U h_par
  linarith

/-- **Co-interior Angles imply Parallel Lines** (同侧内角互补 → 两直线平行):

If two lines `line[ℝ, S, U]` and `line[ℝ, V, X]` are cut by transversal `line[ℝ, R, Y]`
at `T` and `W` respectively, with the betweenness conditions encoding proper crossings,
and if the co-interior (same-side interior) angles sum to `π`:
`∠ R T S + ∠ V₁ W Y = π`, then `line[ℝ, V₁, X] ∥ line[ℝ, S, U]`.

This is the "co-interior angles → parallel" theorem (同侧内角互补则两直线平行),
one of the fundamental results of Chinese high-school parallel-line theory. -/
theorem parallel_of_cointerior_angles {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
  (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
  (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
  (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U)
    (angle_sum : ∠ R T S + ∠ V₁ W Y = π) :
  line[ℝ, V₁, X] ∥ line[ℝ, S, U] := by
  -- The proof follows the structure of UniGeo_Parallel5:
  -- (1) Use the angle sum to deduce ∠ S T W = ∠ X W T (alternate interior angles equal)
  -- (2) Use the side conditions to show the angle signs are opposite
  -- (3) Conclude the direction vectors are parallel (SameRay), hence lines are parallel
  have h_RTW_pi : ∠ R T W = π := Sbtw_RTW.angle₁₂₃_eq_pi
  have h_TWY_pi : ∠ T W Y = π := Sbtw_TWY.angle₁₂₃_eq_pi
  have h_YWT_pi : ∠ Y W T = π := Sbtw_TWY.symm.angle₁₂₃_eq_pi
  have h_VWX_pi : ∠ V₁ W X = π := Sbtw_VWX.angle₁₂₃_eq_pi
  have h_RTS_add_STW : ∠ R T S + ∠ S T W = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi S h_RTW_pi
  have h_STW_eq_VWY : ∠ S T W = ∠ V₁ W Y := by linarith [angle_sum, h_RTS_add_STW]
  have h_VWY_eq_XWT : ∠ V₁ W Y = ∠ X W T := by
    simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_VWX_pi h_YWT_pi
  have h_STW_eq_XWT : ∠ S T W = ∠ X W T := h_STW_eq_VWY.trans h_VWY_eq_XWT
  have hT_mem_RY : T ∈ line[ℝ, R, Y] := T_def.2
  have hW_mem_RY : W ∈ line[ℝ, R, Y] := W_def.2
  have hS_not_mem_RY : S ∉ line[ℝ, R, Y] := V_SameSide_RY_S.right_notMem
  have hS_opposite_U : line[ℝ, R, Y].SOppSide S U :=
    Sbtw_STU.sOppSide_of_notMem_of_mem hS_not_mem_RY hT_mem_RY
  have hS_opposite_X : line[ℝ, R, Y].SOppSide S X :=
    hS_opposite_U.trans_sSameSide X_SameSide_RY_U.symm
  have h_sign_neg_WST : (∡ W X T).sign = -(∡ W S T).sign :=
    hS_opposite_X.oangle_sign_eq_neg hW_mem_RY hT_mem_RY
  have h_sign_neg : (∡ T W X).sign = -(∡ S T W).sign := by
    have h_rot_WXT : (∡ T W X).sign = (∡ W X T).sign := by
      rw [oangle_rotate_sign X T W, oangle_rotate_sign W X T]
    have h_rot_WST : (∡ W S T).sign = (∡ S T W).sign := by
      rw [← oangle_rotate_sign W S T, ← oangle_rotate_sign S T W]
    calc (∡ T W X).sign = (∡ W X T).sign := h_rot_WXT
      _ = -(∡ W S T).sign := h_sign_neg_WST
      _ = -(∡ S T W).sign := by rw [h_rot_WST]
  have h_TW_ne : T ≠ W := Sbtw_RTW.ne_right
  have h_line_TW_eq_RY : line[ℝ, T, W] = line[ℝ, R, Y] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hT_mem_RY hW_mem_RY h_TW_ne
  have h_STW_sign_ne_zero : (∡ S T W).sign ≠ 0 := by
    intro h_zero
    have h_col : Collinear ℝ ({S, T, W} : Set Pt) :=
      (oangle_sign_eq_zero_iff_collinear : (∡ S T W).sign = 0 ↔
        Collinear ℝ ({S, T, W} : Set Pt)).1 h_zero
    have hS_mem_TW : S ∈ line[ℝ, T, W] :=
      h_col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_TW_ne
    exact hS_not_mem_RY <| h_line_TW_eq_RY ▸ hS_mem_TW
  -- Work with vectors x = S -ᵥ T, y = W -ᵥ T, z = W -ᵥ X
  let vx := S -ᵥ T
  let vy := W -ᵥ T
  let vz := W -ᵥ X
  have hvx : vx ≠ 0 := vsub_ne_zero.2 Sbtw_STU.left_ne
  have hvz : vz ≠ 0 := vsub_ne_zero.2 Sbtw_VWX.ne_right
  have h_angle_left : ∠ vx (0 : V) vy = ∠ S T W := by
    simpa [vx, vy] using (angle_vsub_const S T W T)
  have h_angle_right : ∠ vy (0 : V) vz = ∠ T W X := by
    -- vy = W -ᵥ T, vz = W -ᵥ X; use angle_vsub_vsub
    exact angle_vsub_vsub T W X
  have h_angle_vec : ∠ vx (0 : V) vy = ∠ vy (0 : V) vz := by
    rw [h_angle_left, h_angle_right]
    exact h_STW_eq_XWT.trans (angle_comm X W T)
  have h_sign_left : (∡ vx (0 : V) vy).sign = (∡ S T W).sign := by
    simp [EuclideanGeometry.oangle, vx, vy]
  have h_sign_right : (∡ vy (0 : V) vz).sign = (∡ T W X).sign := by
    calc
      (∡ vy (0 : V) vz).sign = (o.oangle (-(T -ᵥ W)) (-(X -ᵥ W))).sign := by
        simp [EuclideanGeometry.oangle, vy, vz]
      _ = (o.oangle (T -ᵥ W) (X -ᵥ W)).sign := by rw [o.oangle_neg_neg]
      _ = (∡ T W X).sign := by simp [EuclideanGeometry.oangle]
  have h_sign_neg_vec : (∡ vx (0 : V) vy).sign = -(∡ vy (0 : V) vz).sign := by
    rw [h_sign_left, h_sign_right]
    simpa [h_sign_neg]
  have h_STW_sign_ne_zero_vec : (∡ vx (0 : V) vy).sign ≠ 0 := by
    rw [h_sign_left]; exact h_STW_sign_ne_zero
  have h_ray : SameRay ℝ vx vz := by
    rcases (angle_eq_iff_oangle_eq_or_wbtw (p₁ := vx) (p₂ := (0 : V)) (p₃ := vy) (p₄ := vz) hvx hvz).1
        h_angle_vec with h_o | h_wbtw | h_wbtw
    · have h_same_sign : (∡ vx (0 : V) vy).sign = (∡ vy (0 : V) vz).sign := by
        simpa [h_o]
      have hzero_right : (∡ vy (0 : V) vz).sign = 0 := by
        have hnegself : -(∡ vy (0 : V) vz).sign = (∡ vy (0 : V) vz).sign := by
          simpa [h_same_sign] using h_sign_neg_vec.symm
        exact SignType.neg_eq_self_iff.mp hnegself
      exact False.elim <| h_STW_sign_ne_zero_vec (by rw [h_same_sign, hzero_right])
    · simpa [vx, vz] using h_wbtw.sameRay_vsub_left
    · exact (by simpa [vx, vz] using h_wbtw.sameRay_vsub_left : SameRay ℝ vz vx).symm
  have h_ray_symm_scaled : ∃ r : ℝ, 0 < r ∧ r • vz = vx :=
    (exists_pos_left_iff_sameRay hvz hvx).2 h_ray.symm
  let r : ℝ := Classical.choose h_ray_symm_scaled
  have hr_pos : 0 < r := (Classical.choose_spec h_ray_symm_scaled).1
  have hr_eq : r • vz = vx := (Classical.choose_spec h_ray_symm_scaled).2
  have h_parallel_ST_WX : line[ℝ, S, T] ∥ line[ℝ, W, X] := by
    refine (affineSpan_pair_parallel_iff_exists_unit_smul (p₁ := S) (q₁ := T)
      (p₂ := W) (q₂ := X)).2 ?_
    refine ⟨Units.mk0 r hr_pos.ne', ?_⟩
    calc
      r • (X -ᵥ W) = r • (-(W -ᵥ X)) := by rw [neg_vsub_eq_vsub_rev]
      _ = -(r • (W -ᵥ X)) := by rw [smul_neg]
      _ = T -ᵥ S := by simpa [vx, vz, neg_vsub_eq_vsub_rev] using congrArg Neg.neg hr_eq
  have h_line_ST_eq_SU : line[ℝ, S, T] = line[ℝ, S, U] :=
    affineSpan_pair_eq_of_right_mem_of_ne T_def.1 Sbtw_STU.left_ne.symm
  have h_line_WX_eq_VX : line[ℝ, W, X] = line[ℝ, V₁, X] :=
    affineSpan_pair_eq_of_left_mem_of_ne W_def.1 Sbtw_VWX.right_ne.symm
  simpa [h_line_WX_eq_VX, h_line_ST_eq_SU] using h_parallel_ST_WX.symm

/-- In the standard transversal configuration, parallelism is equivalent to equality of the
corresponding interior angles. -/
theorem parallel_iff_angle_corresponding_eq {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U) :
    line[ℝ, V₁, X] ∥ line[ℝ, S, U] ↔ ∠ S T W = ∠ V₁ W Y := by
  constructor
  · intro h_par
    exact angle_corresponding_of_parallel_intersections T_def Sbtw_STU Sbtw_TWY W_def Sbtw_VWX
      Sbtw_RTW V_SameSide_RY_S X_SameSide_RY_U h_par
  · intro h_eq
    have h_RTS_add_STW : ∠ R T S + ∠ S T W = π := by
      simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi S Sbtw_RTW.angle₁₂₃_eq_pi
    apply parallel_of_cointerior_angles T_def Sbtw_STU Sbtw_TWY W_def Sbtw_VWX Sbtw_RTW
      V_SameSide_RY_S X_SameSide_RY_U
    linarith

/-- In the standard transversal configuration, parallelism is equivalent to equality of the
alternate-interior angles. -/
theorem parallel_iff_angle_alternate_interior_eq {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U) :
    line[ℝ, V₁, X] ∥ line[ℝ, S, U] ↔ ∠ S T W = ∠ X W T := by
  constructor
  · intro h_par
    exact angle_alternate_interior_of_parallel_intersections T_def Sbtw_STU Sbtw_TWY W_def
      Sbtw_VWX Sbtw_RTW V_SameSide_RY_S X_SameSide_RY_U h_par
  · intro h_eq
    have h_RTS_add_STW : ∠ R T S + ∠ S T W = π := by
      simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi S Sbtw_RTW.angle₁₂₃_eq_pi
    have h_VWX_pi : ∠ V₁ W X = π := Sbtw_VWX.angle₁₂₃_eq_pi
    have h_YWT_pi : ∠ Y W T = π := Sbtw_TWY.symm.angle₁₂₃_eq_pi
    have h_VWY_eq_XWT : ∠ V₁ W Y = ∠ X W T := by
      simpa [angle_comm] using angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_VWX_pi h_YWT_pi
    apply parallel_of_cointerior_angles T_def Sbtw_STU Sbtw_TWY W_def Sbtw_VWX Sbtw_RTW
      V_SameSide_RY_S X_SameSide_RY_U
    linarith [h_RTS_add_STW, h_eq, h_VWY_eq_XWT]

/-- In the standard transversal configuration, parallelism is equivalent to the same-side
interior angles being supplementary. -/
theorem parallel_iff_angle_cointerior_eq_pi {S U V₁ X R Y T W : Pt}
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V₁, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V₁ W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V₁ S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U) :
    line[ℝ, V₁, X] ∥ line[ℝ, S, U] ↔ ∠ R T S + ∠ V₁ W Y = π := by
  constructor
  · intro h_par
    exact angle_cointerior_eq_pi_of_parallel_intersections T_def Sbtw_STU Sbtw_TWY W_def
      Sbtw_VWX Sbtw_RTW V_SameSide_RY_S X_SameSide_RY_U h_par
  · intro h_angle
    exact parallel_of_cointerior_angles T_def Sbtw_STU Sbtw_TWY W_def Sbtw_VWX Sbtw_RTW
      V_SameSide_RY_S X_SameSide_RY_U h_angle

end EuclideanGeometry
