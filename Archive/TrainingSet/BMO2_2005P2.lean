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
