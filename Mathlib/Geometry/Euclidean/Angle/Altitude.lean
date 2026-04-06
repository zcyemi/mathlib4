/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Angles and altitude feet in triangles

This file proves lemmas relating the position of the altitude foot on a side of a triangle to
right, obtuse and acute angles at the vertices.

-/

@[expose] public section

noncomputable section

open scoped CharZero Real RealInnerProductSpace EuclideanGeometry

namespace Affine

namespace Triangle

open EuclideanGeometry Simplex
open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

private theorem not_collinear_points (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ¬ Collinear ℝ ({t.points i₁, t.points i₂, t.points i₃} : Set P) := by
  rw [← affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃]
  exact t.independent

private theorem compl_eq_pair {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := by
  ext i
  have hi : i = i₁ ∨ i = i₂ ∨ i = i₃ := by
    decide +revert
  rcases hi with rfl | rfl | rfl <;>
    simp [h₁₂, h₁₂.symm, h₁₃, h₁₃.symm, h₂₃, h₂₃.symm]

private theorem altitudeFoot_eq_lineMap_and_inner (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ∃ r : ℝ,
      t.altitudeFoot i₁ = AffineMap.lineMap (t.points i₂) (t.points i₃) r ∧
      ⟪t.points i₁ -ᵥ t.points i₂, t.points i₃ -ᵥ t.points i₂⟫ =
        r * ‖t.points i₃ -ᵥ t.points i₂‖ ^ 2 ∧
      ⟪t.points i₁ -ᵥ t.points i₃, t.points i₂ -ᵥ t.points i₃⟫ =
        (1 - r) * ‖t.points i₃ -ᵥ t.points i₂‖ ^ 2 := by
  have hcompl : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := compl_eq_pair h₁₂ h₁₃ h₂₃
  have hfoot_mem : t.altitudeFoot i₁ ∈ line[ℝ, t.points i₂, t.points i₃] := by
    have hmem := t.altitudeFoot_mem_affineSpan_faceOpposite i₁
    rw [Affine.Simplex.range_faceOpposite_points, hcompl, Set.image_pair] at hmem
    simpa using hmem
  obtain ⟨r, hr'⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hfoot_mem
  have hr : t.altitudeFoot i₁ = AffineMap.lineMap (t.points i₂) (t.points i₃) r := hr'.symm
  have hi₂ : t.points i₂ ∈ affineSpan ℝ (Set.range (t.faceOpposite i₁).points) := by
    rw [Affine.Simplex.range_faceOpposite_points, hcompl, Set.image_pair]
    exact mem_affineSpan ℝ (by simp)
  have hi₃ : t.points i₃ ∈ affineSpan ℝ (Set.range (t.faceOpposite i₁).points) := by
    rw [Affine.Simplex.range_faceOpposite_points, hcompl, Set.image_pair]
    exact mem_affineSpan ℝ (by simp)
  have hside_mem :
      t.points i₃ -ᵥ t.points i₂ ∈
        (affineSpan ℝ (Set.range (t.faceOpposite i₁).points)).direction :=
    AffineSubspace.vsub_mem_direction hi₃ hi₂
  have horth_mem :
      t.points i₁ -ᵥ t.altitudeFoot i₁ ∈
        (affineSpan ℝ (Set.range (t.faceOpposite i₁).points)).directionᗮ := by
    simpa [Simplex.altitudeFoot, orthogonalProjectionSpan] using
      vsub_orthogonalProjection_mem_direction_orthogonal
        (affineSpan ℝ (Set.range (t.faceOpposite i₁).points)) (t.points i₁)
  have horth : ⟪t.points i₁ -ᵥ t.altitudeFoot i₁, t.points i₃ -ᵥ t.points i₂⟫ = 0 := by
    exact Submodule.inner_left_of_mem_orthogonal hside_mem horth_mem
  have hfoot_vsub₂ :
      t.altitudeFoot i₁ -ᵥ t.points i₂ = r • (t.points i₃ -ᵥ t.points i₂) := by
    simpa [AffineMap.lineMap_apply] using congrArg (fun p ↦ p -ᵥ t.points i₂) hr
  have hfoot_vsub₃ :
      t.altitudeFoot i₁ -ᵥ t.points i₃ = (1 - r) • (t.points i₂ -ᵥ t.points i₃) := by
    calc
      t.altitudeFoot i₁ -ᵥ t.points i₃ =
          (t.altitudeFoot i₁ -ᵥ t.points i₂) + (t.points i₂ -ᵥ t.points i₃) := by
        rw [vsub_add_vsub_cancel]
      _ = r • (t.points i₃ -ᵥ t.points i₂) + (t.points i₂ -ᵥ t.points i₃) := by
        rw [hfoot_vsub₂]
      _ = (1 - r) • (t.points i₂ -ᵥ t.points i₃) := by
        have hrev : t.points i₂ -ᵥ t.points i₃ = -(t.points i₃ -ᵥ t.points i₂) := by
          rw [neg_vsub_eq_vsub_rev]
        rw [hrev, smul_neg]
        rw [show -(t.points i₃ -ᵥ t.points i₂) = (-1 : ℝ) • (t.points i₃ -ᵥ t.points i₂) by simp]
        rw [← add_smul, ← neg_smul]
        have hcoeff : r + -1 = -(1 - r) := by ring
        simp [hcoeff]
  have horth' : ⟪t.points i₁ -ᵥ t.altitudeFoot i₁, t.points i₂ -ᵥ t.points i₃⟫ = 0 := by
    calc
      ⟪t.points i₁ -ᵥ t.altitudeFoot i₁, t.points i₂ -ᵥ t.points i₃⟫ =
          -⟪t.points i₁ -ᵥ t.altitudeFoot i₁, t.points i₃ -ᵥ t.points i₂⟫ := by
            rw [show t.points i₂ -ᵥ t.points i₃ = -(t.points i₃ -ᵥ t.points i₂) by
                rw [neg_vsub_eq_vsub_rev], inner_neg_right]
      _ = 0 := by simp [horth]
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← vsub_add_vsub_cancel (t.points i₁) (t.altitudeFoot i₁) (t.points i₂), inner_add_left,
      horth, hfoot_vsub₂, zero_add, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  · rw [← vsub_add_vsub_cancel (t.points i₁) (t.altitudeFoot i₁) (t.points i₃), inner_add_left,
      horth', hfoot_vsub₃, zero_add, inner_smul_left, real_inner_self_eq_norm_sq]
    rw [show t.points i₂ -ᵥ t.points i₃ = -(t.points i₃ -ᵥ t.points i₂) by
      rw [neg_vsub_eq_vsub_rev], norm_neg]
    simp

private theorem angle_eq_pi_div_two_iff_inner_eq_zero {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = π / 2 ↔ ⟪p₁ -ᵥ p₂, p₃ -ᵥ p₂⟫ = 0 := by
  simpa [EuclideanGeometry.angle] using
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two
      (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂ : V)).symm

private theorem angle_lt_pi_div_two_iff_inner_pos {p₁ p₂ p₃ : P} (h₁₂ : p₁ ≠ p₂)
    (h₃₂ : p₃ ≠ p₂) :
    ∠ p₁ p₂ p₃ < π / 2 ↔ 0 < ⟪p₁ -ᵥ p₂, p₃ -ᵥ p₂⟫ := by
  constructor
  · intro h
    have hcos : 0 < Real.cos (∠ p₁ p₂ p₃) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [EuclideanGeometry.angle_nonneg p₁ p₂ p₃], h⟩
    have hnorm : 0 < ‖p₁ -ᵥ p₂‖ * ‖p₃ -ᵥ p₂‖ := by
      refine mul_pos ?_ ?_
      · exact norm_pos_iff.mpr (vsub_ne_zero.mpr h₁₂)
      · exact norm_pos_iff.mpr (vsub_ne_zero.mpr h₃₂)
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
    exact mul_pos hcos hnorm
  · intro h
    by_contra h'
    have hge : π / 2 ≤ ∠ p₁ p₂ p₃ := le_of_not_gt h'
    have hcos : Real.cos (∠ p₁ p₂ p₃) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hge
        (by linarith [EuclideanGeometry.angle_le_pi p₁ p₂ p₃])
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm] at h
    have hnorm : 0 ≤ ‖p₁ -ᵥ p₂‖ * ‖p₃ -ᵥ p₂‖ := by positivity
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hcos hnorm)) h

private theorem pi_div_two_lt_angle_iff_inner_neg {p₁ p₂ p₃ : P} (h₁₂ : p₁ ≠ p₂)
    (h₃₂ : p₃ ≠ p₂) :
    π / 2 < ∠ p₁ p₂ p₃ ↔ ⟪p₁ -ᵥ p₂, p₃ -ᵥ p₂⟫ < 0 := by
  constructor
  · intro h
    have hcos : Real.cos (∠ p₁ p₂ p₃) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt h
        (by linarith [EuclideanGeometry.angle_le_pi p₁ p₂ p₃, Real.pi_pos])
    have hnorm : 0 < ‖p₁ -ᵥ p₂‖ * ‖p₃ -ᵥ p₂‖ := by
      refine mul_pos ?_ ?_
      · exact norm_pos_iff.mpr (vsub_ne_zero.mpr h₁₂)
      · exact norm_pos_iff.mpr (vsub_ne_zero.mpr h₃₂)
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
    exact mul_neg_of_neg_of_pos hcos hnorm
  · intro h
    by_contra h'
    have hle : ∠ p₁ p₂ p₃ ≤ π / 2 := le_of_not_gt h'
    have hcos : 0 ≤ Real.cos (∠ p₁ p₂ p₃) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [EuclideanGeometry.angle_nonneg p₁ p₂ p₃], hle⟩
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm] at h
    have hnorm : 0 ≤ ‖p₁ -ᵥ p₂‖ * ‖p₃ -ᵥ p₂‖ := by positivity
    exact (not_lt_of_ge (mul_nonneg hcos hnorm)) h

/-- The altitude foot from `t.points i₁` coincides with `t.points i₂` if and only if the angle at
`t.points i₂` is a right angle. -/
theorem altitudeFoot_eq_point_iff_angle_eq_pi_div_two (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    t.altitudeFoot i₁ = t.points i₂ ↔ ∠ (t.points i₁) (t.points i₂) (t.points i₃) = π / 2 := by
  obtain ⟨r, hr, hinner, -⟩ := altitudeFoot_eq_lineMap_and_inner t h₁₂ h₁₃ h₂₃
  have hside_sq_pos : 0 < ‖t.points i₃ -ᵥ t.points i₂‖ ^ 2 := by
    have hside_pos : 0 < ‖t.points i₃ -ᵥ t.points i₂‖ :=
      norm_pos_iff.mpr (vsub_ne_zero.mpr (t.independent.injective.ne h₂₃.symm))
    nlinarith
  have hfoot : t.altitudeFoot i₁ = t.points i₂ ↔ r = 0 := by
    rw [hr, AffineMap.lineMap_eq_left_iff]
    exact or_iff_right (t.independent.injective.ne h₂₃)
  have hangle : ∠ (t.points i₁) (t.points i₂) (t.points i₃) = π / 2 ↔ r = 0 := by
    rw [angle_eq_pi_div_two_iff_inner_eq_zero, hinner]
    constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_right hside_sq_pos.ne'
    · intro h
      simp [h]
  exact hfoot.trans hangle.symm

/-- The altitude foot from `t.points i₁` lies beyond `t.points i₂` on the side through
`t.points i₂` and `t.points i₃` if and only if the angle at `t.points i₂` is obtuse. -/
theorem sbtw_altitudeFoot_point_point_iff_pi_div_two_lt_angle (t : Triangle ℝ P)
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Sbtw ℝ (t.altitudeFoot i₁) (t.points i₂) (t.points i₃) ↔
      π / 2 < ∠ (t.points i₁) (t.points i₂) (t.points i₃) := by
  obtain ⟨r, hr, hinner, -⟩ := altitudeFoot_eq_lineMap_and_inner t h₁₂ h₁₃ h₂₃
  have hside_sq_pos : 0 < ‖t.points i₃ -ᵥ t.points i₂‖ ^ 2 := by
    have hside_pos : 0 < ‖t.points i₃ -ᵥ t.points i₂‖ :=
      norm_pos_iff.mpr (vsub_ne_zero.mpr (t.independent.injective.ne h₂₃.symm))
    nlinarith
  have hfoot : Sbtw ℝ (t.altitudeFoot i₁) (t.points i₂) (t.points i₃) ↔ r < 0 := by
    have hr' : t.altitudeFoot i₁ = AffineMap.lineMap (t.points i₃) (t.points i₂) (1 - r) := by
      rw [hr]
      exact (AffineMap.lineMap_apply_one_sub (t.points i₃) (t.points i₂) r).symm
    rw [sbtw_iff_right_ne_and_left_mem_image_Ioi]
    constructor
    · rintro ⟨-, s, hs, hs_eq⟩
      have hs' : s = 1 - r := by
        exact (AffineMap.lineMap_injective ℝ (t.independent.injective.ne h₂₃.symm)) <| by
          calc
            AffineMap.lineMap (t.points i₃) (t.points i₂) s = t.altitudeFoot i₁ := hs_eq
            _ = AffineMap.lineMap (t.points i₃) (t.points i₂) (1 - r) := hr'
      rw [Set.mem_Ioi] at hs
      linarith
    · intro hrneg
      refine ⟨(t.independent.injective.ne h₂₃).symm, 1 - r, ?_, hr'.symm⟩
      rw [Set.mem_Ioi]
      linarith
  have hangle : π / 2 < ∠ (t.points i₁) (t.points i₂) (t.points i₃) ↔ r < 0 := by
    rw [pi_div_two_lt_angle_iff_inner_neg (t.independent.injective.ne h₁₂)
      (t.independent.injective.ne h₂₃.symm), hinner]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  exact hfoot.trans hangle.symm

/-- The altitude foot from `t.points i₁` lies strictly between `t.points i₂` and `t.points i₃`
if and only if the angles at those two points are both acute. -/
theorem sbtw_point_altitudeFoot_point_iff_angle_lt_pi_div_two_and_angle_lt_pi_div_two
    (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Sbtw ℝ (t.points i₂) (t.altitudeFoot i₁) (t.points i₃) ↔
      ∠ (t.points i₁) (t.points i₂) (t.points i₃) < π / 2 ∧
        ∠ (t.points i₁) (t.points i₃) (t.points i₂) < π / 2 := by
  obtain ⟨r, hr, hinner₂, hinner₃⟩ := altitudeFoot_eq_lineMap_and_inner t h₁₂ h₁₃ h₂₃
  have hside_sq_pos : 0 < ‖t.points i₃ -ᵥ t.points i₂‖ ^ 2 := by
    have hside_pos : 0 < ‖t.points i₃ -ᵥ t.points i₂‖ :=
      norm_pos_iff.mpr (vsub_ne_zero.mpr (t.independent.injective.ne h₂₃.symm))
    nlinarith
  have hfoot : Sbtw ℝ (t.points i₂) (t.altitudeFoot i₁) (t.points i₃) ↔ 0 < r ∧ r < 1 := by
    rw [hr, sbtw_lineMap_iff]
    simp [Set.mem_Ioo, t.independent.injective.ne h₂₃]
  have hangle₂ : ∠ (t.points i₁) (t.points i₂) (t.points i₃) < π / 2 ↔ 0 < r := by
    rw [angle_lt_pi_div_two_iff_inner_pos (t.independent.injective.ne h₁₂)
      (t.independent.injective.ne h₂₃.symm), hinner₂]
    constructor
    · intro h
      exact (mul_pos_iff_of_pos_right hside_sq_pos).mp h
    · intro h
      exact (mul_pos_iff_of_pos_right hside_sq_pos).2 h
  have hangle₃ : ∠ (t.points i₁) (t.points i₃) (t.points i₂) < π / 2 ↔ r < 1 := by
    rw [angle_lt_pi_div_two_iff_inner_pos (t.independent.injective.ne h₁₃)
      (t.independent.injective.ne h₂₃), hinner₃]
    constructor
    · intro h
      have h' := (mul_pos_iff_of_pos_right hside_sq_pos).mp h
      linarith
    · intro h
      have h' : 0 < 1 - r := by linarith
      exact (mul_pos_iff_of_pos_right hside_sq_pos).2 h'
  exact hfoot.trans <| and_congr hangle₂.symm hangle₃.symm

set_option maxHeartbeats 1200000 in
/-- If the angle at `t.points i₁` is at least `π / 2`, then the altitude foot from
`t.points i₁` lies strictly between the other two vertices. -/
theorem sbtw_point_altitudeFoot_point_of_angle_ge_pi_div_two (t : Triangle ℝ P)
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h_angle : π / 2 ≤ ∠ (t.points i₂) (t.points i₁) (t.points i₃)) :
    Sbtw ℝ (t.points i₂) (t.altitudeFoot i₁) (t.points i₃) := by
  have hnot_col := not_collinear_points t h₁₂ h₁₃ h₂₃
  have hnot_col' : ¬ Collinear ℝ {t.points i₂, t.points i₁, t.points i₃} := by
    have hset : ({t.points i₂, t.points i₁, t.points i₃} : Set P) =
        ({t.points i₁, t.points i₂, t.points i₃} : Set P) := by
      ext p
      simp [or_left_comm]
    rw [hset]
    exact hnot_col
  have hcompl : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := compl_eq_pair h₁₂ h₁₃ h₂₃
  have h : Sbtw ℝ (t.points i₂)
      (↑((orthogonalProjection (affineSpan ℝ ({t.points i₂, t.points i₃} : Set P)))
        (t.points i₁)))
      (t.points i₃) := by
    exact
      (EuclideanGeometry.sbtw_orthogonalProjection_of_angle_ge_pi_div_two
        (p₁ := t.points i₂) (p₂ := t.points i₁) (p₃ := t.points i₃) hnot_col' h_angle rfl)
  have hspan : affineSpan ℝ (Set.range (t.faceOpposite i₁).points) =
      affineSpan ℝ ({t.points i₂, t.points i₃} : Set P) := by
    rw [Affine.Simplex.range_faceOpposite_points, hcompl, Set.image_pair]
  have hproj : (orthogonalProjection (affineSpan ℝ ({t.points i₂, t.points i₃} : Set P))
      (t.points i₁) : P) = t.altitudeFoot i₁ := by
    have hproj' : ((t.faceOpposite i₁).orthogonalProjectionSpan (t.points i₁) : P) =
        (orthogonalProjection (affineSpan ℝ ({t.points i₂, t.points i₃} : Set P)) (t.points i₁) : P) := by
      change (orthogonalProjection (affineSpan ℝ (Set.range (t.faceOpposite i₁).points))
          (t.points i₁) : P) =
        (orthogonalProjection (affineSpan ℝ ({t.points i₂, t.points i₃} : Set P)) (t.points i₁) : P)
      exact orthogonalProjection_congr hspan rfl
    rw [Affine.Simplex.altitudeFoot]
    exact hproj'.symm
  rw [hproj] at h
  exact h

end Triangle

end Affine
