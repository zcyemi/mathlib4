/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib

open scoped Real EuclideanGeometry Similar
open Affine EuclideanGeometry Module AffineSubspace

namespace Triangle10

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]

/-- UniGeo_Triangle10.
In triangles QST and RUV, where angle URV equals angle STQ, and the product of
lengths RV and ST equals the product of lengths RU and QT, prove that angle RUV
equals angle QST.
-/
theorem result (Q S T R U V : Pt)
    (AffineIndependent_QST : AffineIndependent ℝ ![Q, S, T])
    (AffineIndependent_RUV : AffineIndependent ℝ ![R, U, V])
    (URV_eq_STQ : ∠ U R V = ∠ S T Q)
    (RV_ST_eq_RU_QT : dist R V * dist S T = dist R U * dist Q T) :
    ∠ R U V = ∠ Q S T := by
  have h_not_collinear_RUV : ¬ Collinear ℝ ({U, R, V} : Set Pt) := by
    intro h_collinear
    have h_collinear' : Collinear ℝ ({R, U, V} : Set Pt) := by
      convert h_collinear using 1
      ext p
      simp [Set.mem_insert_iff]
      tauto
    exact (affineIndependent_iff_not_collinear_set.1 AffineIndependent_RUV) h_collinear'
  have h_not_collinear_STQ : ¬ Collinear ℝ ({S, T, Q} : Set Pt) := by
    intro h_collinear
    have h_collinear' : Collinear ℝ ({Q, S, T} : Set Pt) := by
      convert h_collinear using 1
      ext p
      simp [Set.mem_insert_iff]
      tauto
    exact (affineIndependent_iff_not_collinear_set.1 AffineIndependent_QST) h_collinear'
  have hsimilar :=
    EuclideanGeometry.similar_of_side_angle_side h_not_collinear_RUV h_not_collinear_STQ
      URV_eq_STQ (by simpa [dist_comm, mul_comm] using RV_ST_eq_RU_QT.symm)
  simpa [angle_comm] using hsimilar.angle_eq_all.2.2

end Triangle10
