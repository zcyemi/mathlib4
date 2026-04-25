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
  have h_RTS_add_STW : ∠ R T S + ∠ S T W = π := by
    simpa [angle_comm, add_comm] using angle_add_angle_eq_pi_of_angle_eq_pi S h_RTW_pi
  have h_STW_eq_VWY : ∠ S T W = ∠ V W Y := by
    linarith [angle_sum, h_RTS_add_STW]
  have h_VWY_eq_TWV : ∠ V W Y = ∠ T W V := by
    simpa [angle_comm] using (angle_eq_angle_of_angle_eq_pi V h_TWY_pi).symm
  have h_STW_eq_TWV : ∠ S T W = ∠ T W V := by
    rw [← h_VWY_eq_TWV]
    exact h_STW_eq_VWY
  sorry
