/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Side
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Similarity
import Mathlib.Topology.MetricSpace.Similarity

set_option linter.unusedSectionVars false

open scoped Real EuclideanGeometry Affine Congruent
open Affine EuclideanGeometry Module
open AffineSubspace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

namespace BMO2_2003P2


noncomputable section

-- 1. P、A、B、C 四点共圆 → ∠APB = ∠ACB。 (同弧所对圆周角相等)
-- 2. ∠ADP = ∠ACB → ∠ADP = ∠APB。 (等量代换)
-- 3. A、D、B 三点共线且 A、P、B 三点共线 → ∠DAP = ∠PAB。 (共线关系)
-- 4. ∠ADP = ∠APB 且 ∠DAP = ∠PAB → △ADP ∽ △APB。 (AA 相似)
-- 5. △ADP ∽ △APB → AD / AP = AP / AB。 (相似三角形性质)
-- 6. AD / AP = AP / AB → AP^2 = AD * AB。 (比例化简)
-- 7. AB = 4AD → AP^2 = 4AD^2。 (代入步骤 6)
-- 8. AP^2 = 4AD^2 → AP = 2AD。 (长度为正)
-- 9. △ADP ∽ △APB → PD / PB = AD / AP。 (相似三角形性质)
-- 10. PD / PB = AD / AP 且 AP = 2AD → PD / PB = 1 / 2。 (代入)
-- 11. PD / PB = 1 / 2 → PB = 2PD。 (比例化简)

/-- BMO Round 2 2003 Problem 2.
Let ABC be a triangle and let D be a point on AB such that
4 * AD = AB. The half-line ℓ is drawn on the same side of AB as C,
starting from D and making an angle of θ with DA where θ = ∠ ACB.
If the circumcircle of ABC meets the half-line ℓ at P, show that
PB = 2 * PD.
-/
structure Cfg where
  (A B C D P : Pt)
  (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
  {triangle_ABC : Triangle ℝ Pt}
  (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
  (sbtw_A_D_B : Sbtw ℝ A D B)
  (four_mul_dist_AD_eq_dist_AB : 4 * dist A D = dist A B)
  (P_sSameSide_AB_C : line[ℝ, A, B].SSameSide P C)
  (angle_ADP_eq_angle_ACB : ∠ A D P = ∠ A C B)
  (P_mem_circumsphere : P ∈ triangle_ABC.circumsphere)


@[implicit_reducible]
def someOrientation [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

variable {V Pt}

namespace Cfg

variable (cfg : Cfg (V := V) (Pt := Pt))

/-! ### Configuration properties -/

theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

theorem A_ne_D : cfg.A ≠ cfg.D :=
  cfg.sbtw_A_D_B.left_ne

theorem D_ne_B : cfg.D ≠ cfg.B :=
  cfg.sbtw_A_D_B.right_ne.symm

theorem not_collinear_ABC : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC

theorem P_not_mem_AB : cfg.P ∉ line[ℝ, cfg.A, cfg.B] :=
  cfg.P_sSameSide_AB_C.left_notMem

theorem not_collinear_APB : ¬Collinear ℝ ({cfg.A, cfg.P, cfg.B} : Set Pt) := by
  intro hcol
  have hPmem : cfg.P ∈ line[ℝ, cfg.A, cfg.B] := by
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B
  exact cfg.P_not_mem_AB hPmem

theorem affineIndependent_APB : AffineIndependent ℝ ![cfg.A, cfg.P, cfg.B] :=
  affineIndependent_iff_not_collinear_set.2 cfg.not_collinear_APB

theorem affineIndependent_ADP : AffineIndependent ℝ ![cfg.A, cfg.D, cfg.P] := by
  have hpab : AffineIndependent ℝ ![cfg.P, cfg.A, cfg.B] := cfg.affineIndependent_APB.comm_left
  apply AffineIndependent.reverse_of_three
  apply AffineIndependent.comm_right
  rw [affineIndependent_iff_affineIndependent_collinear_ne (p₃ := cfg.B)
    cfg.sbtw_A_D_B.wbtw.collinear cfg.sbtw_A_D_B.left_ne cfg.sbtw_A_D_B.left_ne_right]
  exact hpab

theorem cospherical_ABCP : Cospherical ({cfg.A, cfg.B, cfg.C, cfg.P} : Set Pt) := by
  rw [cospherical_iff_exists_sphere]
  refine ⟨cfg.triangle_ABC.circumsphere, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simpa [cfg.triangle_ABC_def] using cfg.triangle_ABC.mem_circumsphere (i := 0)
  · simpa [cfg.triangle_ABC_def] using cfg.triangle_ABC.mem_circumsphere (i := 1)
  · simpa [cfg.triangle_ABC_def] using cfg.triangle_ABC.mem_circumsphere (i := 2)
  · simpa using cfg.P_mem_circumsphere


theorem P_ne_A : cfg.P ≠ cfg.A :=
  cfg.affineIndependent_APB.injective.ne (by decide : (1 : Fin 3) ≠ 0)

theorem P_ne_B : cfg.P ≠ cfg.B :=
  cfg.affineIndependent_APB.injective.ne (by decide : (1 : Fin 3) ≠ 2)

theorem C_ne_A : cfg.C ≠ cfg.A :=
  cfg.A_ne_C.symm

theorem C_ne_B : cfg.C ≠ cfg.B :=
  cfg.B_ne_C.symm

/-! ### Inscribed-angle step -/

section oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_APB_eq_two_zsmul_oangle_ACB :
    (2 : ℤ) • ∡ cfg.A cfg.P cfg.B = (2 : ℤ) • ∡ cfg.A cfg.C cfg.B := by
  have hAPCB : Cospherical ({cfg.A, cfg.P, cfg.C, cfg.B} : Set Pt) := by
    grind [Set.insert_comm, Set.pair_comm, cfg.cospherical_ABCP]
  exact hAPCB.two_zsmul_oangle_eq cfg.P_ne_A cfg.P_ne_B cfg.C_ne_A cfg.C_ne_B

theorem oangle_APB_sign_eq_oangle_ACB_sign :
    (∡ cfg.A cfg.P cfg.B).sign = (∡ cfg.A cfg.C cfg.B).sign := by
  have hA_mem : cfg.A ∈ line[ℝ, cfg.A, cfg.B] := left_mem_affineSpan_pair ℝ cfg.A cfg.B
  have hB_mem : cfg.B ∈ line[ℝ, cfg.A, cfg.B] := right_mem_affineSpan_pair ℝ cfg.A cfg.B
  exact (cfg.P_sSameSide_AB_C.oangle_sign_eq hA_mem hB_mem).symm

theorem oangle_ACB_sign_ne_zero : (∡ cfg.A cfg.C cfg.B).sign ≠ 0 := by
  intro h
  have h' : Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) := by
    simpa [Set.insert_comm, Set.pair_comm] using
      ((oangle_sign_eq_zero_iff_collinear :
        (∡ cfg.A cfg.C cfg.B).sign = 0 ↔ Collinear ℝ ({cfg.A, cfg.C, cfg.B} : Set Pt)).1 h)
  exact cfg.not_collinear_ABC h'

theorem oangle_APB_eq_oangle_ACB : ∡ cfg.A cfg.P cfg.B = ∡ cfg.A cfg.C cfg.B := by
  have htwo : (2 : ℤ) • ∡ cfg.A cfg.C cfg.B = (2 : ℤ) • ∡ cfg.A cfg.P cfg.B := by
    simpa [eq_comm] using cfg.two_zsmul_oangle_APB_eq_two_zsmul_oangle_ACB
  exact (Real.Angle.two_zsmul_eq_iff_eq cfg.oangle_ACB_sign_ne_zero
    cfg.oangle_APB_sign_eq_oangle_ACB_sign.symm).1 htwo |>.symm

theorem angle_APB_eq_angle_ACB : ∠ cfg.A cfg.P cfg.B = ∠ cfg.A cfg.C cfg.B := by
  have h1 : ∠ cfg.A cfg.P cfg.B = |(∡ cfg.A cfg.P cfg.B).toReal| :=
    angle_eq_abs_oangle_toReal cfg.P_ne_A.symm cfg.P_ne_B.symm
  have h2 : ∠ cfg.A cfg.C cfg.B = |(∡ cfg.A cfg.C cfg.B).toReal| :=
    angle_eq_abs_oangle_toReal cfg.C_ne_A.symm cfg.C_ne_B.symm
  simp [h1, h2, cfg.oangle_APB_eq_oangle_ACB]

end oriented

/-! ### Similarity chain -/

theorem angle_DAP_eq_angle_PAB : ∠ cfg.D cfg.A cfg.P = ∠ cfg.P cfg.A cfg.B := by
  have h := cfg.sbtw_A_D_B.angle_eq_left cfg.P
  simpa [angle_comm] using h

theorem angle_ADP_eq_angle_APB :
    ∠ cfg.A cfg.D cfg.P = ∠ cfg.A cfg.P cfg.B := by
  calc
    ∠ cfg.A cfg.D cfg.P = ∠ cfg.A cfg.C cfg.B := cfg.angle_ADP_eq_angle_ACB
    _ = ∠ cfg.A cfg.P cfg.B := cfg.angle_APB_eq_angle_ACB.symm

theorem not_collinear_ADP : ¬Collinear ℝ ({cfg.A, cfg.D, cfg.P} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ADP

theorem angle_DPA_eq_angle_PBA :
    ∠ cfg.D cfg.P cfg.A = ∠ cfg.P cfg.B cfg.A := by
  have hsum_ADP : ∠ cfg.A cfg.D cfg.P + ∠ cfg.D cfg.P cfg.A + ∠ cfg.P cfg.A cfg.D = π :=
    angle_add_angle_add_angle_eq_pi cfg.P cfg.sbtw_A_D_B.left_ne.symm
  have hsum_APB : ∠ cfg.A cfg.P cfg.B + ∠ cfg.P cfg.B cfg.A + ∠ cfg.B cfg.A cfg.P = π :=
    angle_add_angle_add_angle_eq_pi cfg.B cfg.P_ne_A
  have hBAP : ∠ cfg.B cfg.A cfg.P = ∠ cfg.P cfg.A cfg.B := by
    rw [angle_comm]
  have hPAD : ∠ cfg.P cfg.A cfg.D = ∠ cfg.P cfg.A cfg.B := by
    simpa [angle_comm] using cfg.angle_DAP_eq_angle_PAB
  linarith [hsum_ADP, hsum_APB, cfg.angle_ADP_eq_angle_APB, hBAP, hPAD]

theorem similar_ADP_APB :
    Similar ![cfg.A, cfg.D, cfg.P] ![cfg.A, cfg.P, cfg.B] :=
  similar_of_angle_angle cfg.not_collinear_ADP cfg.angle_ADP_eq_angle_APB cfg.angle_DPA_eq_angle_PBA

theorem exists_pos_dist_eq :
    ∃ r, 0 < r ∧
      dist cfg.A cfg.D = r * dist cfg.A cfg.P ∧
      dist cfg.A cfg.P = r * dist cfg.A cfg.B ∧
      dist cfg.D cfg.P = r * dist cfg.P cfg.B := by
  obtain ⟨r, hr_pos, hdist⟩ := cfg.similar_ADP_APB.exists_pos_dist_eq
  refine ⟨r, hr_pos, ?_, ?_, ?_⟩
  · simpa using hdist 0 1
  · simpa using hdist 0 2
  · simpa using hdist 1 2

/-! ### Length conclusion -/

theorem AP_sq_eq_AD_mul_AB :
    dist cfg.A cfg.P ^ 2 = dist cfg.A cfg.D * dist cfg.A cfg.B := by
  obtain ⟨r, hr_pos, hAD_eq, hAP_eq, hDP_eq⟩ := cfg.exists_pos_dist_eq
  grind

theorem AP_eq_two_mul_AD :
    dist cfg.A cfg.P = 2 * dist cfg.A cfg.D := by
  have h1 := cfg.AP_sq_eq_AD_mul_AB
  rw [← cfg.four_mul_dist_AD_eq_dist_AB] at h1
  have hsq : dist cfg.A cfg.P ^ 2 = (2 * dist cfg.A cfg.D) ^ 2 := by
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hAP_nonneg : 0 ≤ dist cfg.A cfg.P := dist_nonneg
    have hAD_nonneg : 0 ≤ 2 * dist cfg.A cfg.D := by
      nlinarith [show 0 ≤ dist cfg.A cfg.D from dist_nonneg]
    linarith

theorem PB_eq_two_mul_PD : dist cfg.P cfg.B = 2 * dist cfg.P cfg.D := by
  obtain ⟨r, hr_pos, hAD_eq, hAP_eq, hDP_eq⟩ := cfg.exists_pos_dist_eq
  have hAD_pos : 0 < dist cfg.A cfg.D := dist_pos.mpr cfg.A_ne_D
  rw [cfg.AP_eq_two_mul_AD] at hAD_eq
  have hr : r = (1 / 2 : ℝ) := by
    nlinarith
  have hDP' : dist cfg.P cfg.D = (1 / 2 : ℝ) * dist cfg.P cfg.B := by
    simpa [dist_comm, hr] using hDP_eq
  nlinarith

theorem result : dist cfg.P cfg.B = 2 * dist cfg.P cfg.D :=
  cfg.PB_eq_two_mul_PD

end Cfg

end

theorem result {A B C D P : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (sbtw_A_D_B : Sbtw ℝ A D B)
    (four_mul_dist_AD_eq_dist_AB : 4 * dist A D = dist A B)
    (P_sSameSide_AB_C : line[ℝ, A, B].SSameSide P C)
    (angle_ADP_eq_angle_ACB : ∠ A D P = ∠ A C B)
    (P_mem_circumsphere : P ∈ triangle_ABC.circumsphere) :
    dist P B = 2 * dist P D := by
  let cfg : Cfg (V := V) (Pt := Pt) :=
    ⟨A, B, C, D, P, affineIndependent_ABC, triangle_ABC_def, sbtw_A_D_B,
      four_mul_dist_AD_eq_dist_AB, P_sSameSide_AB_C, angle_ADP_eq_angle_ACB,
      P_mem_circumsphere⟩
  exact cfg.result

end BMO2_2003P2
