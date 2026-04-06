/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Sphere.Tangent

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2024P3

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2024 Problem 3.
 Let 𝐴𝐵𝐶 be an acute-angled triangle with 𝐴𝐵 > 𝐴𝐶. Let 𝑃 be the intersection of the
tangents to the circumcircle of 𝐴𝐵𝐶 at 𝐵 and 𝐶. The line through the midpoints of line
segments 𝑃𝐵 and 𝑃𝐶 meets lines 𝐴𝐵 and 𝐴𝐶 at 𝑋 and 𝑌 respectively.
Prove that the quadrilateral 𝐴𝑋𝑃𝑌 is cyclic. -/
theorem result {A B C P X Y: Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (acute_ABC : triangle_ABC.AcuteAngled)
    (AB_gt_AC : dist A B > dist A C)
    {ω : Sphere Pt}
    (P_def : triangle_ABC.circumsphere.IsTangentAt B line[ℝ, P, B] ∧ triangle_ABC.circumsphere.IsTangentAt C line[ℝ, P, C])
    (X_def : X ∈ line[ℝ, A, B] ⊓ line[ℝ, midpoint ℝ P B, midpoint ℝ P C])
    (Y_def : Y ∈ line[ℝ, A, C] ⊓ line[ℝ, midpoint ℝ P B, midpoint ℝ P C]) :
    Cospherical {A, X, P, Y} := by
  sorry

end BMO2_2024P3
