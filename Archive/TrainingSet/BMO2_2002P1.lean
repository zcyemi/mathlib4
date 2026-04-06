/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Simplex

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2002P1

-- 1. DE ⟂ AB 且 DF ⟂ AC → ∠AED = 90° 且 ∠AFD = 90°。 (垂直定义)
-- 2. ∠AED = 90° 且 ∠AFD = 90° → A、E、D、F 四点共圆，且 AD 为该圆的直径。 (同圆判定)
-- 3. A、E、D、F 四点共圆且 AD 为外接圆直径 → EF = AD * sin A。 (正弦定理)
-- 4. 在直角三角形 ABD 中 → AD = AB * sin B。 (正弦定义)
-- 5. EF = AD * sin A 且 AD = AB * sin B → EF = AB * sin A * sin B。 (代入)
-- 6. 在三角形 ABC 中，设外接圆半径为 R → AB = 2R * sin C。 (正弦定理)
-- 7. EF = AB * sin A * sin B 且 AB = 2R * sin C → EF = 2R * sin A * sin B * sin C。 (代入)
-- 8. 从顶点 B 或 C 出发作对应构造 → 所得线段长度同样等于 2R * sin A * sin B * sin C。 (表达式对称性)
-- 9. 三种构造所得线段长度都等于 2R * sin A * sin B * sin C → EF 与所选顶点无关。 (结论)


attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- A configuration satisfying the conditions of the problem. -/
structure Cfg where
  (A B C : Pt)
  (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
  {triangle_ABC : Triangle ℝ Pt}
  (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
  (acute_ABC : triangle_ABC.AcuteAngled)
  (i j k : Fin 3) (i_ne_j : i ≠ j) (i_ne_k : i ≠ k) (j_ne_k : j ≠ k)
  (Di : Pt) (Dj : Pt) (Ei : Pt) (Fi : Pt) (Ej : Pt) (Fj : Pt)
  (Di_def : Di = triangle_ABC.altitudeFoot i)
  (Dj_def : Dj = triangle_ABC.altitudeFoot j)
  (Ei_def : Ei = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {i, j})) Di)
  (Fi_def : Fi = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {i, k})) Di)
  (Ej_def : Ej = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {j, i})) Dj)
  (Fj_def : Fj = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {j, k})) Dj)

namespace Cfg

variable (cfg : Cfg (V := V) (Pt := Pt))

/-- The configuration has symmetry between the two chosen vertices `i` and `j`. -/
def symm (cfg : Cfg (V := V) (Pt := Pt)) : Cfg (V := V) (Pt := Pt) where
  A := cfg.A
  B := cfg.B
  C := cfg.C
  affineIndependent_ABC := cfg.affineIndependent_ABC
  triangle_ABC := cfg.triangle_ABC
  triangle_ABC_def := cfg.triangle_ABC_def
  acute_ABC := cfg.acute_ABC
  i := cfg.j
  j := cfg.i
  k := cfg.k
  i_ne_j := cfg.i_ne_j.symm
  i_ne_k := cfg.j_ne_k
  j_ne_k := cfg.i_ne_k
  Di := cfg.Dj
  Dj := cfg.Di
  Ei := cfg.Ej
  Fi := cfg.Fj
  Ej := cfg.Ei
  Fj := cfg.Fi
  Di_def := cfg.Dj_def
  Dj_def := cfg.Di_def
  Ei_def := cfg.Ej_def
  Fi_def := cfg.Fj_def
  Ej_def := cfg.Ei_def
  Fj_def := cfg.Fi_def

/-! ### Configuration properties -/

theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

theorem not_collinear_ABC : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC

/-! ### Proof steps -/

theorem DE_perp_AB :
    line[ℝ, cfg.Di, cfg.Ei].direction ⟂ line[ℝ, cfg.A, cfg.B].direction := by
  sorry

theorem DF_perp_AC :
    line[ℝ, cfg.Di, cfg.Fi].direction ⟂ line[ℝ, cfg.A, cfg.C].direction := by

  sorry

theorem AEiDiFi_cyclic : Cospherical ({cfg.A, cfg.Ei, cfg.Di, cfg.Fi} : Set Pt) := by
  sorry

/-- `EF = AD * sin A` in the configuration. -/
theorem EF_eq_AD_sinA :
    dist cfg.Ei cfg.Fi = dist cfg.A cfg.Di * Real.sin (∠ cfg.B cfg.A cfg.C) := by
  sorry

/-- `AD = AB * sin B` in triangle `ABD`. -/
theorem AD_eq_AB_sinB :
    dist cfg.A cfg.Di = dist cfg.A cfg.B * Real.sin (∠ cfg.C cfg.B cfg.A) := by
  sorry

/-- `AB = 2R * sin C` for triangle `ABC`. -/
theorem AB_eq_2R_sinC :
    dist cfg.A cfg.B =
      2 * cfg.triangle_ABC.circumradius * Real.sin (∠ cfg.A cfg.C cfg.B) := by
  sorry

/-- The length of `EiFi` in terms of the circumradius and angles of `ABC`. -/
theorem EiFi_length_formula :
    dist cfg.Ei cfg.Fi =
      2 * cfg.triangle_ABC.circumradius *
        Real.sin (∠ cfg.B cfg.A cfg.C) *
        Real.sin (∠ cfg.C cfg.B cfg.A) *
        Real.sin (∠ cfg.A cfg.C cfg.B) := by
  have h_EF_AD_sinA := cfg.EF_eq_AD_sinA
  have h_AD_AB_sinB := cfg.AD_eq_AB_sinB
  have h_AB_2R_sinC := cfg.AB_eq_2R_sinC

  calc
    dist cfg.Ei cfg.Fi = dist cfg.A cfg.Di * Real.sin (∠ cfg.B cfg.A cfg.C) := h_EF_AD_sinA
    _ =
        dist cfg.A cfg.B *
          Real.sin (∠ cfg.C cfg.B cfg.A) *
          Real.sin (∠ cfg.B cfg.A cfg.C) := by
            rw [h_AD_AB_sinB]
    _ =
        2 * cfg.triangle_ABC.circumradius *
          Real.sin (∠ cfg.B cfg.A cfg.C) *
          Real.sin (∠ cfg.C cfg.B cfg.A) *
          Real.sin (∠ cfg.A cfg.C cfg.B) := by
            rw [h_AB_2R_sinC]
            ring

/-- The same length formula for `EjFj`. -/
theorem EjFj_length_formula :
    dist cfg.Ej cfg.Fj =
      2 * cfg.triangle_ABC.circumradius *
        Real.sin (∠ cfg.B cfg.A cfg.C) *
        Real.sin (∠ cfg.C cfg.B cfg.A) *
        Real.sin (∠ cfg.A cfg.C cfg.B) := by
  have h := cfg.symm.EiFi_length_formula
  simpa [Cfg.symm] using h

/-- The final result, deduced from the two length formulas. -/
theorem result : dist cfg.Ei cfg.Fi = dist cfg.Ej cfg.Fj := by
  have h_EiFi := cfg.EiFi_length_formula
  have h_EjFj := cfg.EjFj_length_formula
  exact h_EiFi.trans h_EjFj.symm

end Cfg

/-- BMO Round 2 2002 Problem 1.
The altitude from one of the vertices of an acute-angled
triangle ABC meets the opposite side at D. From D
perpendiculars DE and DF are drawn to the other two sides.
Prove that the length of EF is the same whichever vertex is chosen
-/
theorem bmo2_2002_p1 [Fact (finrank ℝ V = 2)] (A B C Di Dj Ei Ej Fi Fj : Pt)
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (acute_ABC : triangle_ABC.AcuteAngled)
    (i j k : Fin 3) (i_ne_j : i ≠ j) (i_ne_k : i ≠ k) (j_ne_k : j ≠ k)
    (Di_def : Di = triangle_ABC.altitudeFoot i)
    (Dj_def : Dj = triangle_ABC.altitudeFoot j)
    (Ei_def : Ei = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {i, j})) Di)
    (Fi_def : Fi = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {i, k})) Di)
    (Ej_def : Ej = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {j, i})) Dj)
    (Fj_def : Fj = orthogonalProjection (affineSpan ℝ (triangle_ABC.points '' {j, k})) Dj) :
    dist Ei Fi = dist Ej Fj := by

  let cfg : Cfg (V := V) (Pt := Pt) :=
   (⟨A, B, C, affineIndependent_ABC, triangle_ABC_def, acute_ABC, i, j, k, i_ne_j, i_ne_k, j_ne_k, Di, Dj, Ei, Fi, Ej, Fj, Di_def, Dj_def, Ei_def, Fi_def, Ej_def, Fj_def⟩)
  let ret := cfg.result
  exact ret

end BMO2_2002P1
