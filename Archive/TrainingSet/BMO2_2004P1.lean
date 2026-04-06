/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.Simplex


open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2004P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2004 Problem 1.
 Let ABC be an equilateral triangle and D an internal point of the
side BC. A circle, tangent to BC at D, cuts AB internally at M
and N, and AC internally at P and Q.
Show that BD + AM + AN = CD + AP + AQ.
-/
theorem result {A B C D M N P Q : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (equilateral_ABC : triangle_ABC.Equilateral)
    (Sbtw_BDC : Sbtw ℝ B D C)
    (ω : Sphere Pt)
    (ω_tangent_at_D : ω.IsTangentAt D line[ℝ, B, C])
    (M_N_def : {M, N} = (ω : Set Pt) ⊓ line[ℝ, A, B])
    (M_ne_N : M ≠ N)
    (Sbtw_AMB : Sbtw ℝ A M B)
    (Sbtw_ANB : Sbtw ℝ A N B)
    (P_Q_def : {P, Q} = (ω : Set Pt) ⊓ line[ℝ, A, C])
    (P_ne_Q : P ≠ Q)
    (Sbtw_APC : Sbtw ℝ A P C)
    (Sbtw_AQC : Sbtw ℝ A Q C) :
    dist B D + dist A M + dist A N = dist C D + dist A P + dist A Q := by
  sorry

end BMO2_2004P1
