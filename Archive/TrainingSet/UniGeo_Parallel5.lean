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

/-- UniGeo_Parallel5.
Given lines SU, VX, and RY.line SU and RY intersecting at point T, with
T between S and U, and W between T and Y; lines VX and RY intersecting at
point W, with W between V and X, and T between R and W; V is on the same
side of RY as S, X is on the same side of RY as U, and the sum of angles
RTS and VWY equals two right angles, prove that lines VX and SU are parallel.
-/

theorem result
    (S U V X R Y T W : Pt)
    (S_ne_U : S ≠ U)
    (V_ne_X : V ≠ X)
    (R_ne_Y : R ≠ Y)
    (T_def : T ∈ line[ℝ, S, U] ⊓ line[ℝ, R, Y])
    (Sbtw_STU : Sbtw ℝ S T U)
    (Sbtw_TWY : Sbtw ℝ T W Y)
    (W_def : W ∈ line[ℝ, V, X] ⊓ line[ℝ, R, Y])
    (Sbtw_VWX : Sbtw ℝ V W X)
    (Sbtw_RTW : Sbtw ℝ R T W)
    (V_SameSide_RY_S : line[ℝ, R, Y].SSameSide V S)
    (X_SameSide_RY_U : line[ℝ, R, Y].SSameSide X U)
    (angle_sum : ∠ R T S + ∠ V W Y = π) :
    line[ℝ, V, X] ∥ line[ℝ, S, U] := by
  have h_RTW_pi : ∠ R T W = π := Sbtw_RTW.angle₁₂₃_eq_pi
  have h_TWY_pi : ∠ T W Y = π := Sbtw_TWY.angle₁₂₃_eq_pi
  have h_YWT_pi : ∠ Y W T = π := Sbtw_TWY.symm.angle₁₂₃_eq_pi
  have h_VWX_pi : ∠ V W X = π := Sbtw_VWX.angle₁₂₃_eq_pi
  have h_RTS_add_STW : ∠ R T S + ∠ S T W = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi S h_RTW_pi
  have h_STW_eq_VWY : ∠ S T W = ∠ V W Y := by
    linarith [angle_sum, h_RTS_add_STW]
  have h_VWY_eq_XWT : ∠ V W Y = ∠ X W T := by
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
    calc
      (∡ T W X).sign = (∡ W X T).sign := h_rot_WXT
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
    have hS_mem_TW : S ∈ line[ℝ, T, W] := by
      exact h_col.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h_TW_ne
    exact hS_not_mem_RY <| h_line_TW_eq_RY ▸ hS_mem_TW
  let x := S -ᵥ T
  let y := W -ᵥ T
  let z := W -ᵥ X
  have hx : x ≠ 0 := vsub_ne_zero.2 Sbtw_STU.left_ne
  have hz : z ≠ 0 := vsub_ne_zero.2 Sbtw_VWX.ne_right
  have h_angle_left : ∠ x (0 : _) y = ∠ S T W := by
    simpa [x, y] using (angle_vsub_const S T W T)

  have h_angle_right : ∠ y (0 : _) z = ∠ T W X := by
    sorry
    -- simpa [y, z] using
    --   (angle_neg (T -ᵥ W) (0 : _) (X -ᵥ W)).trans (angle_vsub_const T W X W)
  have h_angle_vec : ∠ x (0 : _) y = ∠ y (0 : _) z := by
    sorry
    -- rw [h_angle_left, h_angle_right, h_STW_eq_XWT]
  have h_sign_left : (∡ x (0 : _) y).sign = (∡ S T W).sign := by
    simp [EuclideanGeometry.oangle, x, y]
  have h_sign_right : (∡ y (0 : _) z).sign = (∡ T W X).sign := by
    calc
      (∡ y (0 : _) z).sign = (o.oangle (-(T -ᵥ W)) (-(X -ᵥ W))).sign := by
        simp [EuclideanGeometry.oangle, y, z]
      _ = (o.oangle (T -ᵥ W) (X -ᵥ W)).sign := by rw [o.oangle_neg_neg]
      _ = (∡ T W X).sign := by simp [EuclideanGeometry.oangle]
  have h_sign_neg_vec : (∡ x (0 : _) y).sign = -(∡ y (0 : _) z).sign := by
    rw [h_sign_left, h_sign_right]
    have h1 := h_sign_neg.symm
    rw [← h1]

  have h_STW_sign_ne_zero_vec : (∡ x (0 : _) y).sign ≠ 0 := by
    rw [h_sign_left]
    exact h_STW_sign_ne_zero
  have h_ray : SameRay ℝ x z := by
    rcases (angle_eq_iff_oangle_eq_or_wbtw (p₁ := x) (p₂ := (0 : _)) (p₃ := y) (p₄ := z) hx hz).1
        h_angle_vec with h_o | h_wbtw | h_wbtw
    · have h_same_sign : (∡ x (0 : _) y).sign = (∡ y (0 : _) z).sign := by
        simpa [h_o]
      have hzero_right : (∡ y (0 : _) z).sign = 0 := by
        have hnegself : -(∡ y (0 : _) z).sign = (∡ y (0 : _) z).sign := by
          rw [← h_same_sign] at h_sign_neg_vec
          exact h_sign_neg_vec.symm
        exact SignType.neg_eq_self_iff.mp hnegself
      have hzero_left : (∡ x (0 : _) y).sign = 0 := by rw [h_same_sign, hzero_right]
      exact False.elim <| h_STW_sign_ne_zero_vec hzero_left
    · simpa [x, z] using h_wbtw.sameRay_vsub_left
    · exact (by simpa [x, z] using h_wbtw.sameRay_vsub_left : SameRay ℝ z x).symm
  have h_ray_symm_scaled : ∃ r : ℝ, 0 < r ∧ r • z = x :=
    (exists_pos_left_iff_sameRay hz hx).2 h_ray.symm
  let r : ℝ := Classical.choose h_ray_symm_scaled
  have hr_pos : 0 < r := (Classical.choose_spec h_ray_symm_scaled).1
  have hr_eq : r • z = x := (Classical.choose_spec h_ray_symm_scaled).2
  have h_parallel_ST_WX : line[ℝ, S, T] ∥ line[ℝ, W, X] := by
    refine (affineSpan_pair_parallel_iff_exists_unit_smul (p₁ := S) (q₁ := T)
      (p₂ := W) (q₂ := X)).2 ?_
    refine ⟨Units.mk0 r hr_pos.ne', ?_⟩
    simpa [x, z, neg_vsub_eq_vsub_rev, neg_smul] using congrArg Neg.neg hr_eq
  have h_line_ST_eq_SU : line[ℝ, S, T] = line[ℝ, S, U] := by
    exact affineSpan_pair_eq_of_right_mem_of_ne T_def.1 Sbtw_STU.left_ne.symm
  have h_line_WX_eq_VX : line[ℝ, W, X] = line[ℝ, V, X] := by
    exact affineSpan_pair_eq_of_left_mem_of_ne W_def.1 Sbtw_VWX.ne_right

    simpa [h_line_WX_eq_VX, h_line_ST_eq_SU] using h_parallel_ST_WX.symm
