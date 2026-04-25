import Mathlib.Geometry.Euclidean.Congruence

open scoped Real EuclideanGeometry Congruent
open Affine EuclideanGeometry Module AffineSubspace

namespace Congruent8

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- UniGeo_Congruent8.
Given triangles PST, QRS, and PQS, where P is on the opposite side of line QS from R, Q
is on the same side of line PS as R, Q is on the opposite side of line PS from T, P is
on the same side of line QS as T, angle RQS equals angle SPT, length PT equals length QR,
length PQ equals length QS, and length QS equals length SP, prove that triangles PST and
QSR are congruent.
-/
theorem result
    (P Q R S T : Pt)
    (AffiIndependent_PST : AffineIndependent ℝ ![P, S, T])
    (AffiIndependent_QRS : AffineIndependent ℝ ![Q, R, S])
    (AffiIndependent_PQS : AffineIndependent ℝ ![P, Q, S])
    (P_opposide_QS_R : line[ℝ, Q, S].SOppSide P R)
    (Q_sameside_PS_R : line[ℝ, P, S].SSameSide Q R)
    (Q_opposite_PS_T : line[ℝ, P, S].SOppSide Q T)
    (P_sameside_QS_T : line[ℝ, Q, S].SSameSide P T)
    (RQS_eq_SPT : ∠ R Q S = ∠ S P T)
    (PT_eq_QR : dist P T = dist Q R)
    (PQ_eq_QS : dist P Q = dist Q S)
    (QS_eq_SP : dist Q S = dist S P) :
    ![P, S, T] ≅ ![Q, S, R] := by
  let _ := AffiIndependent_PST
  let _ := AffiIndependent_QRS
  let _ := AffiIndependent_PQS
  let _ := P_opposide_QS_R
  let _ := Q_sameside_PS_R
  let _ := Q_opposite_PS_T
  let _ := P_sameside_QS_T
  let _ := PQ_eq_QS
  have h_angle : ∠ S P T = ∠ S Q R := by
    simpa [angle_comm] using RQS_eq_SPT.symm
  have h_SP_eq_SQ : dist S P = dist S Q := by
    simpa [dist_comm] using QS_eq_SP.symm
  have h_PS_eq_QS : dist P S = dist Q S := by
    simpa [dist_comm] using h_SP_eq_SQ
  have h_SPT_QSR : ![S, P, T] ≅ ![S, Q, R] := by
    exact EuclideanGeometry.side_angle_side h_angle h_SP_eq_SQ PT_eq_QR
  have h_ST_eq_SR : dist S T = dist S R := by
    simpa [dist_comm] using h_SPT_QSR.dist_eq 0 2
  exact EuclideanGeometry.side_side_side h_PS_eq_QS h_ST_eq_SR
    (by simpa [dist_comm] using PT_eq_QR)

end Congruent8
