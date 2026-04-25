/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib

open scoped Real EuclideanGeometry Similar
open Affine EuclideanGeometry Module AffineSubspace

namespace Similar19

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- UniGeo_Similar19.
In triangles HIK and IJK, where K lies between H and J, angles HKI and IKJ
are right angles, and angle HIJ is a right angle, prove that triangles IJK
and HIK are similar.
-/
theorem result
    (H I K J : Pt)
    (AffiIndependent_HIK : AffineIndependent ℝ ![H, I, K])
    (AffiIndependent_IJK : AffineIndependent ℝ ![I, J, K])
    (Sbtw_HKJ : Sbtw ℝ H K J)
    (HKI_right : ∠ H K I = π / 2)
    (IKJ_right : ∠ I K J = π / 2)
    (HIJ_right : ∠ H I J = π / 2) :
    ![I, J, K] ∼ ![H, I, K] := by
  let _ := AffiIndependent_HIK
  have h_not_collinear_IJK : ¬Collinear ℝ ({I, J, K} : Set Pt) :=
    affineIndependent_iff_not_collinear_set.1 AffiIndependent_IJK
  have h_not_collinear_IKJ : ¬Collinear ℝ ({I, K, J} : Set Pt) := by
    simpa [Set.insert_comm, Set.pair_comm] using h_not_collinear_IJK
  have h_I_ne_H : I ≠ H :=
    AffiIndependent_HIK.injective.ne (by decide : (1 : Fin 3) ≠ 0)
  have h_KHI_eq_JHI : ∠ K H I = ∠ J H I := by
    simpa [angle_comm] using Sbtw_HKJ.angle_eq_right I
  have h_IJH_eq_HIK : ∠ I J H = ∠ H I K := by
    have hsum_HIK : ∠ H I K + ∠ I K H + ∠ K H I = π :=
      angle_add_angle_add_angle_eq_pi K h_I_ne_H
    have hsum_HIJ : ∠ H I J + ∠ I J H + ∠ J H I = π :=
      angle_add_angle_add_angle_eq_pi J h_I_ne_H
    have h_IKH_right : ∠ I K H = π / 2 := by
      simpa [angle_comm] using HKI_right
    linarith [hsum_HIK, hsum_HIJ, h_IKH_right, HIJ_right, h_KHI_eq_JHI]
  have h_KJI_eq_KIH : ∠ K J I = ∠ K I H := by
    have h_KJI_eq_HJI : ∠ K J I = ∠ H J I := by
      simpa [angle_comm] using Sbtw_HKJ.symm.angle_eq_right I
    calc
      ∠ K J I = ∠ H J I := h_KJI_eq_HJI
      _ = ∠ H I K := by simpa [angle_comm] using h_IJH_eq_HIK
      _ = ∠ K I H := by rw [angle_comm]
  have h_IJK_eq_HIK : ∠ I J K = ∠ H I K := by
    calc
      ∠ I J K = ∠ I J H := by simpa [angle_comm] using Sbtw_HKJ.symm.angle_eq_right I
      _ = ∠ H I K := h_IJH_eq_HIK
  have h_JKI_eq_IKH : ∠ J K I = ∠ I K H := by
    calc
      ∠ J K I = ∠ I K J := by rw [angle_comm]
      _ = π / 2 := IKJ_right
      _ = ∠ I K H := by simpa [angle_comm] using HKI_right.symm
  exact EuclideanGeometry.similar_of_angle_angle h_not_collinear_IJK h_IJK_eq_HIK h_JKI_eq_IKH

end Similar19
