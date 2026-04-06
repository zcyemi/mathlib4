/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Sphere.Tangent

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2021P3

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2021 Problem 3.
Let 𝐴𝐵𝐶 be a triangle with 𝐴𝐵 > 𝐴𝐶. Its circumcircle is Γ and its incentre is 𝐼. Let 𝐷 be
the contact point of the incircle of 𝐴𝐵𝐶 with 𝐵𝐶.
Let 𝐾 be the point on Γ such that ∠𝐴𝐾𝐼 is a right angle.
Prove that 𝐴𝐼 and 𝐾𝐷 meet on Γ.
-/
theorem result {A B C I D K : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (AB_gt_AC : dist A B > dist A C)
    {Γ : Sphere Pt}
    {Γ_def : Γ = triangle_ABC.circumsphere}
    (I_def : I = triangle_ABC.incenter)
    (D_def : D ∈ (triangle_ABC.insphere : Set Pt) ⊓ line[ℝ, B, C])
    (K_def : K ∈ triangle_ABC.circumsphere ∧ ∠ A K I = π / 2) :
    ∃ (E : Pt), E ∈ line[ℝ, A, I] ⊓ line[ℝ, K, D] ∧ E ∈ Γ := by
  sorry

end BMO2_2021P3
