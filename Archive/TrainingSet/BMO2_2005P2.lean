/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Incenter
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Sphere.Basic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2005P2

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

@[implicit_reducible]
def someOrientation [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

-- 证明思路:
-- 先把 D 看成两个子三角形 ABD 与 ADC 的公共顶点。由 ∠BAC = 120° 且 AD 平分 ∠BAC，可知 AC 是 △ABD 在 A 处的外角平分线，AB 是 △ADC 在 A 处的外角平分线。于是 E 是 △ABD 的旁心，F 是 △ADC 的旁心，从而 DE 与 DF 分别平分 D 处的外角。最后把这两个角平分关系相加，得到 ∠EDF = 90°，于是 D 落在以 EF 为直径的圆上。

-- 证明步骤:

-- 1. ∠BAC = 120° 且 AD 平分 ∠BAC → ∠BAD = ∠CAD = 60°。 (角平分线定义)
-- 2. 延长 BA 至点 X → ∠XAC = 180° - ∠BAC = 60°。 (平角定义)
-- 3. ∠XAC = 60° 且 ∠CAD = 60° → AC 平分 △ABD 在 A 处的外角。 (等量代换)
-- 4. BE 平分 ∠ABD 且 AC 平分 △ABD 在 A 处的外角 → E 是 △ABD 关于顶点 B 的旁心。 (旁心定义)
-- 5. E 是 △ABD 的旁心 → DE 平分 △ABD 在 D 处的外角。 (旁心性质)
-- 6. B、D、C 三点共线 → △ABD 在 D 处的外角是 ∠ADC。 (外角定义)
-- 7. DE 平分 ∠ADC → ∠ADE = 1 / 2 ∠ADC。 (角平分线性质)
-- 8. 延长 CA 至点 Y → ∠YAB = 180° - ∠BAC = 60°。 (平角定义)
-- 9. ∠YAB = 60° 且 ∠BAD = 60° → AB 平分 △ADC 在 A 处的外角。 (等量代换)
-- 10. CF 平分 ∠ACD 且 AB 平分 △ADC 在 A 处的外角 → F 是 △ADC 关于顶点 C 的旁心。 (旁心定义)
-- 11. F 是 △ADC 的旁心 → DF 平分 △ADC 在 D 处的外角。 (旁心性质)
-- 12. B、D、C 三点共线 → △ADC 在 D 处的外角是 ∠ADB。 (外角定义)
-- 13. DF 平分 ∠ADB → ∠ADF = 1 / 2 ∠ADB。 (角平分线性质)
-- 14. ∠EDF = ∠ADE + ∠ADF → ∠EDF = 1 / 2 ∠ADC + 1 / 2 ∠ADB。 (等量代换)
-- 15. ∠ADC + ∠ADB = 180° → ∠EDF = 90°。 (代数化简)
-- 16. ∠EDF = 90° → D 在以 EF 为直径的圆上。 (圆周角定理逆定理)

/-- BMO Round 2 2005 Problem 2.
In triangle ABC, ∠ BAC = 120◦. Let the angle bisectors of angles
A,B and C meet the opposite sides in D,E and F respectively.
Prove that the circle on diameter EF passes through D
-/
structure Cfg where
  (A B C D E F : Pt)
  (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
  {triangle_ABC : Triangle ℝ Pt}
  (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
  (angle_BAC_eq : ∠ B A C = π * 2 / 3)
  (D_def : D ∈ line[ℝ, B, C] ⊓ line[ℝ, A, triangle_ABC.incenter])
  (E_def : E ∈ line[ℝ, A, C] ⊓ line[ℝ, B, triangle_ABC.incenter])
  (F_def : F ∈ line[ℝ, A, B] ⊓ line[ℝ, C, triangle_ABC.incenter])

namespace Cfg

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]
variable [Module.Oriented ℝ V (Fin 2)]

variable (cfg : Cfg (V := V) (Pt := Pt))

/-! ### Configuration properties -/

theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

theorem D_mem_BC : cfg.D ∈ line[ℝ, cfg.B, cfg.C] := cfg.D_def.1

theorem D_mem_AI : cfg.D ∈ line[ℝ, cfg.A, cfg.triangle_ABC.incenter] := cfg.D_def.2

theorem E_mem_AC : cfg.E ∈ line[ℝ, cfg.A, cfg.C] := cfg.E_def.1

theorem E_mem_BI : cfg.E ∈ line[ℝ, cfg.B, cfg.triangle_ABC.incenter] := cfg.E_def.2

theorem F_mem_AB : cfg.F ∈ line[ℝ, cfg.A, cfg.B] := cfg.F_def.1

theorem F_mem_CI : cfg.F ∈ line[ℝ, cfg.C, cfg.triangle_ABC.incenter] := cfg.F_def.2

/-- The incenter bisects angle `A`. -/
theorem angle_BAI_eq_angle_IAC :
    ∠ cfg.B cfg.A cfg.triangle_ABC.incenter = ∠ cfg.triangle_ABC.incenter cfg.A cfg.C := by
  have h := cfg.triangle_ABC.oangle_incenter_eq (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide)
  have hleft : ∠ cfg.B cfg.A cfg.triangle_ABC.incenter =
      |(∡ cfg.B cfg.A cfg.triangle_ABC.incenter).toReal| := by
    simpa using (angle_eq_abs_oangle_toReal cfg.A_ne_B.symm (cfg.triangle_ABC.incenter_ne_point 0))
  have hright : ∠ cfg.triangle_ABC.incenter cfg.A cfg.C =
      |(∡ cfg.triangle_ABC.incenter cfg.A cfg.C).toReal| := by
    simpa using (angle_eq_abs_oangle_toReal (cfg.triangle_ABC.incenter_ne_point 0).symm cfg.A_ne_C.symm)
  simp [h, hleft, hright]

/-- The incenter bisects angle `B`. -/
theorem angle_ABI_eq_angle_IBC :
    ∠ cfg.A cfg.B cfg.triangle_ABC.incenter = ∠ cfg.triangle_ABC.incenter cfg.B cfg.C := by
  have h := cfg.triangle_ABC.oangle_incenter_eq (i₁ := 1) (i₂ := 2) (i₃ := 0)
    (by decide) (by decide) (by decide)
  have hleft : ∠ cfg.A cfg.B cfg.triangle_ABC.incenter =
      |(∡ cfg.A cfg.B cfg.triangle_ABC.incenter).toReal| := by
    simpa using (angle_eq_abs_oangle_toReal cfg.B_ne_C.symm (cfg.triangle_ABC.incenter_ne_point 1))
  have hright : ∠ cfg.triangle_ABC.incenter cfg.B cfg.C =
      |(∡ cfg.triangle_ABC.incenter cfg.B cfg.C).toReal| := by
    simpa using (angle_eq_abs_oangle_toReal (cfg.triangle_ABC.incenter_ne_point 1).symm cfg.B_ne_C.symm)
  simp [h, hleft, hright]

/-- The incenter bisects angle `C`. -/
theorem angle_ACI_eq_angle_ICB :
    ∠ cfg.A cfg.C cfg.triangle_ABC.incenter = ∠ cfg.triangle_ABC.incenter cfg.C cfg.B := by
  have h := cfg.triangle_ABC.oangle_incenter_eq (i₁ := 2) (i₂ := 0) (i₃ := 1)
    (by decide) (by decide) (by decide)
  have hleft : ∠ cfg.A cfg.C cfg.triangle_ABC.incenter =
      |(∡ cfg.A cfg.C cfg.triangle_ABC.incenter).toReal| := by
    simpa using (angle_eq_abs_oangle_toReal cfg.C_ne_B.symm (cfg.triangle_ABC.incenter_ne_point 2))
  have hright : ∠ cfg.triangle_ABC.incenter cfg.C cfg.B =
      |(∡ cfg.triangle_ABC.incenter cfg.C cfg.B).toReal| := by
    simpa using (angle_eq_abs_oangle_toReal (cfg.triangle_ABC.incenter_ne_point 2).symm cfg.C_ne_B.symm)
  simp [h, hleft, hright]

axiom angle_BAC_eq_two_mul_angle_BAI :
    ∠ cfg.B cfg.A cfg.C = 2 * ∠ cfg.B cfg.A cfg.triangle_ABC.incenter

axiom angle_ABC_eq_angle_ACE :
    ∠ cfg.A cfg.B cfg.C = ∠ cfg.A cfg.C cfg.triangle_ABC.incenter

axiom angle_ACB_eq_angle_ABF :
    ∠ cfg.A cfg.C cfg.B = ∠ cfg.A cfg.B cfg.triangle_ABC.incenter

/-! ### Triangle decomposition at D -/

axiom angle_ADE_eq_half_angle_ADC :
    ∠ cfg.A cfg.D cfg.E = (1 / 2 : ℝ) * ∠ cfg.A cfg.D cfg.C

axiom angle_ADF_eq_half_angle_ADB :
    ∠ cfg.A cfg.D cfg.F = (1 / 2 : ℝ) * ∠ cfg.A cfg.D cfg.B

axiom angle_EDF_eq_add :
    ∠ cfg.E cfg.D cfg.F = ∠ cfg.E cfg.D cfg.A + ∠ cfg.A cfg.D cfg.F

axiom angle_EDF_eq_pi_two : ∠ cfg.E cfg.D cfg.F = π / 2

/-! ### Final conclusion -/

axiom result : cfg.D ∈ Sphere.ofDiameter cfg.E cfg.F

end Cfg

theorem result {A B C D E F : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (angle_BAC_eq : ∠ B A C = π * 2 / 3)
    (D_def : D ∈ line[ℝ, B, C] ⊓ line[ℝ, A, triangle_ABC.incenter])
    (E_def : E ∈ line[ℝ, A, C] ⊓ line[ℝ, B, triangle_ABC.incenter])
    (F_def : F ∈ line[ℝ, A, B] ⊓ line[ℝ, C, triangle_ABC.incenter]) :
    D ∈ Sphere.ofDiameter E F := by
  let cfg : Cfg (V := V) (Pt := Pt) :=
    ⟨A, B, C, D, E, F, affineIndependent_ABC, triangle_ABC_def, angle_BAC_eq, D_def, E_def,
      F_def⟩
  simpa using cfg.result

end BMO2_2005P2
