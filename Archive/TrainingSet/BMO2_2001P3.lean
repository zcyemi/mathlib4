/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Analysis.Convex.Between
import Mathlib.Geometry.Euclidean.Projection

open scoped Real EuclideanGeometry
open Affine EuclideanGeometry Module AffineSubspace
namespace BMO2_2001P3

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]
variable [Module.Oriented ℝ V (Fin 2)]

/-- BMO Round 2 2001 Problem 3.
A triangle ABC has ∠ ACB > ∠ ABC.
The internal bisector of ∠ BAC meets BC at D.
The point E on AB is such that ∠ EDB = 90◦.
The point F on AC is such that ∠ BED = ∠ DEF.
Show that ∠ BAD = ∠ FDC
--/
theorem result {A B C D E F : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (ACB_gt_ABC : ∠ A C B > ∠ A B C)
    (bisector_AD : ∡ ((orthogonalProjection line[ℝ, A, D] B): Pt) A B  =
      ∡ C A ((orthogonalProjection line[ℝ, A, D] C): Pt))
    (Sbtw_BDC : Sbtw ℝ B D C)
    (E_mem_AB : E ∈ line[ℝ, A, B])
    (angle_EDB : ∠ E D B = π / 2)
    (F_mem_AC : F ∈ line[ℝ, A, C])
    (angle_BED_eq_angle_DEF : ∠ B E D = ∠ D E F) :
    ∠ B A D = ∠ F D C := by
  sorry

end BMO2_2001P3
