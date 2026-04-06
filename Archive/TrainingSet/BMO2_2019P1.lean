/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.PerpBisector

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2019P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2019 Problem 1.
Let ABC be a triangle. Let L be the line through B perpendicular to
AB. The perpendicular from A to BC meets L at the point D. The
perpendicular bisector of BC meets L at the point P. Let E be the foot
of the perpendicular from D to AC.
Prove that triangle BPE is isosceles.
-/

theorem result {A B C L D P E : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (L_perp : line[ℝ, A, B].direction ⟂ line[ℝ, B, L].direction)
    (AD_perp : line[ℝ, A, D].direction ⟂ line[ℝ, B, C].direction)
    (D_def : D ∈ line[ℝ, A, D] ⊓ line[ℝ, B, L])
    (P_def : P ∈ (perpBisector B C) ⊓ line[ℝ, B, L])
    (E_def : E = orthogonalProjection (line[ℝ, A, C]) D) :
    dist P B = dist P E := by
  sorry

end BMO2_2019P1
