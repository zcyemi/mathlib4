/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib

open scoped Real EuclideanGeometry Congruent
open Affine EuclideanGeometry Module AffineSubspace
open InnerProductSpace

namespace Congruent15

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- UniGeo_Congruent15.
In triangles STU and SUV, where V lies on the opposite side of line SU from T, angle UVS
is a right angle, angle USV equals angle SUT, and angle STU is a right angle, prove that
the length of UV equals the length of ST.
-/
theorem result
    (S T U V : Pt)
    (AffiIndependent_STU : AffineIndependent ℝ ![S, T, U])
    (AffiIndependent_SUV : AffineIndependent ℝ ![S, U, V])
    (V_opposite_SU_T : line[ℝ, S, U].SOppSide V T)
    (UVS_right : ∠ U V S = π / 2)
    (USV_eq_SUT : ∠ U S V = ∠ S U T)
    (STU_right : ∠ S T U = π / 2) :
    dist U V = dist S T := by
  let _ := AffiIndependent_SUV
  let _ := V_opposite_SU_T
  have h_not_collinear : ¬Collinear ℝ ({S, T, U} : Set Pt) :=
    affineIndependent_iff_not_collinear_set.1 AffiIndependent_STU
  have h_STU_eq_UVS : ∠ S T U = ∠ U V S := by
    rw [STU_right, UVS_right]
  have h_TUS_eq_VSU : ∠ T U S = ∠ V S U := by
    simpa [angle_comm] using USV_eq_SUT.symm
  have h_congr : ![S, T, U] ≅ ![U, V, S] :=
    EuclideanGeometry.angle_angle_side h_not_collinear h_STU_eq_UVS h_TUS_eq_VSU
      (by simp [dist_comm])
  simpa using (h_congr.dist_eq 0 1).symm

end Congruent15
