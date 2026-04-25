/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Triangle
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
  have hAB : dist A B = dist A C := by
    have htri := Triangle.acuteAngled_iff_angle_lt.mp acute_ABC
    have hA_lt : ∠ B A C < π / 2 := by
      simpa [triangle_ABC_def, angle_comm] using htri.2.2
    have hA_ne_pi : ∠ B A C ≠ π := by
      exact ne_of_lt (lt_of_lt_of_lt hA_lt (by
        have hπ : (π / 2 : ℝ) < π := by
          have hπ0 : (0 : ℝ) < π := by positivity
          linarith
        exact hπ))
    have hABC : ∠ A B C = ∠ A C B := by
      simpa [angle_comm] using angle_B_eq_angle_C
    exact dist_eq_of_angle_eq_angle_of_angle_ne_pi hABC hA_ne_pi

  have hO_mem : O ∈ AffineSubspace.perpBisector B C := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq']
    have hOB : dist O B = triangle_ABC.circumradius := by
      simpa [O_def, dist_comm] using triangle_ABC.dist_circumcenter_eq_circumradius 1
    have hOC : dist O C = triangle_ABC.circumradius := by
      simpa [O_def, dist_comm] using triangle_ABC.dist_circumcenter_eq_circumradius 2
    simpa [dist_comm] using hOB.trans hOC.symm

  have hA_mem : A ∈ AffineSubspace.perpBisector B C := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq']
    simpa [dist_comm] using hAB

  sorry

end BMO2_2009P2
