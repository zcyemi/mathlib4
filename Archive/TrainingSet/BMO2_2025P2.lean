/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.PerpBisector

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2025P2

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2025 Problem 2.
In an acute-angled triangle 𝐴𝐵𝐶 with 𝐴𝐵 < 𝐴𝐶, the incentre is 𝐼 and the perpendicular
bisector of 𝐵𝐶 meets 𝐵𝐼 at 𝑃 and 𝐶𝐼 at 𝑄. The circles 𝐵𝐼𝑄 and 𝐶𝐼𝑃 meet again at 𝑋. The
lines 𝐴𝑋 and 𝐵𝐶 meet at 𝐷.
Prove that 𝐷 lies on the circle AQP -/
theorem result {A B C I P Q X D: Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (acute_ABC : triangle_ABC.AcuteAngled)
    (AB_lt_AC : dist A B < dist A C)
    (I_def : I = triangle_ABC.incenter)
    (P_def : P ∈ (perpBisector B C) ⊓ line[ℝ, B, I])
    (Q_def : Q ∈ (perpBisector B C) ⊓ line[ℝ, C, I])
    (indep_BIQ : AffineIndependent ℝ ![B, I, Q])
    (indep_CIP : AffineIndependent ℝ ![C, I, P])
    {ω₁ ω₂ : Sphere Pt}
    (ω₁_def : ω₁ = (⟨_ , indep_BIQ⟩ : Triangle ℝ Pt).circumsphere)
    (ω₂_def : ω₂ = (⟨_ , indep_CIP⟩ : Triangle ℝ Pt).circumsphere)
    (X_def : X ∈ ω₁ ∧ X ∈ ω₂ ∧ X ≠ I)
    (D_def : D ∈ line[ℝ, A, X] ⊓ line[ℝ, B, C]) :
    Cospherical {D, A, Q, P} := by
  sorry

end BMO2_2025P2
