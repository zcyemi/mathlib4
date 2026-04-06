/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.MongePoint

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2009P2

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2009 Problem 2.
Let ABC be an acute-angled triangle with ∠ B = ∠ C. Let the
circumcentre be O and the orthocentre be H. Prove that the centre
of the circle BOH lies on the line AB. The circumcentre of a triangle
is the centre of its circumcircle. The orthocentre of a triangle is the
point where its three altitudes meet
-/

theorem result {A B C O H : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (acute_ABC : triangle_ABC.AcuteAngled)
    (angle_B_eq_angle_C : ∠ A B C = ∠ B C A)
    (O_def : O = triangle_ABC.circumcenter)
    (H_def : H = triangle_ABC.orthocenter)
    (indep_BOH : AffineIndependent ℝ ![B, O, H]) :
    (⟨_,indep_BOH⟩ : Triangle ℝ Pt).circumcenter ∈ line[ℝ, A, B] := by
  sorry

end BMO2_2009P2
