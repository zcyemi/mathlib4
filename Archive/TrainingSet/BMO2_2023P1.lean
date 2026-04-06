/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2023P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2023 Problem 1.
Let 𝐴𝐵𝐶 be a triangle with an obtuse angle 𝐴 and incentre 𝐼. Circles 𝐴𝐵𝐼 and 𝐴𝐶𝐼 intersect
𝐵𝐶 again at 𝑋 and 𝑌 respectively. The lines 𝐴𝑋 and 𝐵𝐼 meet at 𝑃, and the lines 𝐴𝑌 and 𝐶𝐼
meet at 𝑄. Prove that 𝐵𝐶𝑄𝑃 is cyclic. -/
theorem result {A B C I P Q X Y: Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (obtuse_angle_A : ∠ B A C > π / 2)
    (I_def : I = triangle_ABC.incenter)
    (indep_ABI : AffineIndependent ℝ ![A, B, I])
    (indep_ACI : AffineIndependent ℝ ![A, C, I])
    (X_def : X = (⟨_ , indep_ABI⟩ : Triangle ℝ Pt).circumsphere.secondInter B (C -ᵥ B))
    (X_ne_B : X ≠ B)
    (Y_def : Y = (⟨_ , indep_ACI⟩ : Triangle ℝ Pt).circumsphere.secondInter C (B -ᵥ C))
    (Y_ne_C : Y ≠ C)
    (P_def : P ∈ line[ℝ, A, X] ⊓ line[ℝ, B, I])
    (Q_def : Q ∈ line[ℝ, A, Y] ⊓ line[ℝ, C, I]) :
    Cospherical {B, C, Q, P} := by
  sorry

end BMO2_2023P1
