/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Sphere.Basic

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2005P2

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2005 Problem 2.
In triangle ABC, ∠ BAC = 120◦. Let the angle bisectors of angles
A,B and C meet the opposite sides in D,E and F respectively.
Prove that the circle on diameter EF passes through D
-/
theorem result {A B C D E F : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (angle_BAC_eq : ∠ B A C = π * 2 / 3)
    (D_def : D ∈ line[ℝ, B, C] ⊓ line[ℝ, A, triangle_ABC.incenter])
    (E_def : E ∈ line[ℝ, A, C] ⊓ line[ℝ, B, triangle_ABC.incenter])
    (F_def : F ∈ line[ℝ, A, B] ⊓ line[ℝ, C, triangle_ABC.incenter]) :
    D ∈ Sphere.ofDiameter E F := by
  sorry

end BMO2_2005P2
