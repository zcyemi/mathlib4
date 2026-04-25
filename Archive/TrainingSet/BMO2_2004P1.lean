/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.Simplex

set_option linter.style.longLine false


open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2004P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- BMO Round 2 2004 Problem 1.
 Let ABC be an equilateral triangle and D an internal point of the
side BC. A circle, tangent to BC at D, cuts AB internally at M
and N, and AC internally at P and Q.
Show that BD + AM + AN = CD + AP + AQ.
-/
structure Cfg where
  (A B C D M N P Q : Pt)
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
  (Sbtw_AQC : Sbtw ℝ A Q C)

namespace Cfg

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

variable (cfg : Cfg (V := V) (Pt := Pt))

/-! ### Configuration properties -/

theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

theorem hM_mem : cfg.M ∈ (cfg.ω : Set Pt) ∩ line[ℝ, cfg.A, cfg.B] := by
  have h : cfg.M ∈ ({cfg.M, cfg.N} : Set Pt) := by simp
  simpa [cfg.M_N_def] using h

theorem hN_mem : cfg.N ∈ (cfg.ω : Set Pt) ∩ line[ℝ, cfg.A, cfg.B] := by
  have h : cfg.N ∈ ({cfg.M, cfg.N} : Set Pt) := by simp
  simpa [cfg.M_N_def] using h

theorem hP_mem : cfg.P ∈ (cfg.ω : Set Pt) ∩ line[ℝ, cfg.A, cfg.C] := by
  have h : cfg.P ∈ ({cfg.P, cfg.Q} : Set Pt) := by simp
  simpa [cfg.P_Q_def] using h

theorem hQ_mem : cfg.Q ∈ (cfg.ω : Set Pt) ∩ line[ℝ, cfg.A, cfg.C] := by
  have h : cfg.Q ∈ ({cfg.P, cfg.Q} : Set Pt) := by simp
  simpa [cfg.P_Q_def] using h

theorem hMN_eq_lineAB : line[ℝ, cfg.M, cfg.N] = line[ℝ, cfg.A, cfg.B] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne cfg.hM_mem.2 cfg.hN_mem.2 cfg.M_ne_N

theorem hPQ_eq_lineAC : line[ℝ, cfg.P, cfg.Q] = line[ℝ, cfg.A, cfg.C] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne cfg.hP_mem.2 cfg.hQ_mem.2 cfg.P_ne_Q

theorem hA_mem_lineMN : cfg.A ∈ line[ℝ, cfg.M, cfg.N] := by
  rw [cfg.hMN_eq_lineAB]
  exact left_mem_affineSpan_pair ℝ cfg.A cfg.B

theorem hB_mem_lineMN : cfg.B ∈ line[ℝ, cfg.M, cfg.N] := by
  rw [cfg.hMN_eq_lineAB]
  exact right_mem_affineSpan_pair ℝ cfg.A cfg.B

theorem hA_mem_linePQ : cfg.A ∈ line[ℝ, cfg.P, cfg.Q] := by
  rw [cfg.hPQ_eq_lineAC]
  exact left_mem_affineSpan_pair ℝ cfg.A cfg.C

theorem hC_mem_linePQ : cfg.C ∈ line[ℝ, cfg.P, cfg.Q] := by
  rw [cfg.hPQ_eq_lineAC]
  exact right_mem_affineSpan_pair ℝ cfg.A cfg.C

theorem hBD_eq_lineBC : line[ℝ, cfg.B, cfg.D] = line[ℝ, cfg.B, cfg.C] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne
    (left_mem_affineSpan_pair ℝ cfg.B cfg.C) cfg.Sbtw_BDC.wbtw.mem_affineSpan cfg.Sbtw_BDC.left_ne

theorem hCD_eq_lineBC : line[ℝ, cfg.C, cfg.D] = line[ℝ, cfg.B, cfg.C] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne
    (right_mem_affineSpan_pair ℝ cfg.B cfg.C) cfg.Sbtw_BDC.wbtw.mem_affineSpan cfg.Sbtw_BDC.right_ne

theorem hω_tangent_BD : cfg.ω.IsTangentAt cfg.D line[ℝ, cfg.B, cfg.D] := by
  simpa [cfg.hBD_eq_lineBC] using cfg.ω_tangent_at_D

theorem hω_tangent_CD : cfg.ω.IsTangentAt cfg.D line[ℝ, cfg.C, cfg.D] := by
  simpa [cfg.hCD_eq_lineBC] using cfg.ω_tangent_at_D

/-! ### Power and secant relations -/

theorem hAM_mul_AN_eq_AP_mul_AQ : dist cfg.A cfg.M * dist cfg.A cfg.N = dist cfg.A cfg.P * dist cfg.A cfg.Q := by
  calc
    dist cfg.A cfg.M * dist cfg.A cfg.N = |cfg.ω.power cfg.A| :=
      cfg.ω.mul_dist_eq_abs_power cfg.hA_mem_lineMN cfg.hM_mem.1 cfg.hN_mem.1
    _ = dist cfg.A cfg.P * dist cfg.A cfg.Q := by
      symm
      exact cfg.ω.mul_dist_eq_abs_power cfg.hA_mem_linePQ cfg.hP_mem.1 cfg.hQ_mem.1

theorem hBD_sq_eq_BM_mul_BN : dist cfg.B cfg.D * dist cfg.B cfg.D = dist cfg.B cfg.M * dist cfg.B cfg.N := by
  simpa [pow_two] using
    Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant cfg.hM_mem.1 cfg.hN_mem.1 cfg.hB_mem_lineMN cfg.hω_tangent_BD

theorem hCD_sq_eq_CP_mul_CQ : dist cfg.C cfg.D * dist cfg.C cfg.D = dist cfg.C cfg.P * dist cfg.C cfg.Q := by
  simpa [pow_two] using
    Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant cfg.hP_mem.1 cfg.hQ_mem.1 cfg.hC_mem_linePQ cfg.hω_tangent_CD

/-! ### Segment decompositions -/

theorem hAB_eq_AC : dist cfg.A cfg.B = dist cfg.A cfg.C := by
  simpa [cfg.triangle_ABC_def] using
    cfg.equilateral_ABC.dist_eq (i₁ := (0 : Fin 3)) (i₂ := 1) (i₃ := 0) (i₄ := 2)
      (by decide) (by decide)

theorem hAB_eq_BC : dist cfg.A cfg.B = dist cfg.B cfg.C := by
  simpa [cfg.triangle_ABC_def] using
    cfg.equilateral_ABC.dist_eq (i₁ := (0 : Fin 3)) (i₂ := 1) (i₃ := 1) (i₄ := 2)
      (by decide) (by decide)

theorem hAB_eq_AM_add_BM : dist cfg.A cfg.B = dist cfg.A cfg.M + dist cfg.B cfg.M := by
  simpa [dist_comm, add_comm] using
    dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr cfg.Sbtw_AMB)

theorem hAB_eq_AN_add_BN : dist cfg.A cfg.B = dist cfg.A cfg.N + dist cfg.B cfg.N := by
  simpa [dist_comm, add_comm] using
    dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr cfg.Sbtw_ANB)

theorem hAC_eq_AP_add_CP : dist cfg.A cfg.C = dist cfg.A cfg.P + dist cfg.C cfg.P := by
  simpa [dist_comm, add_comm] using
    dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr cfg.Sbtw_APC)

theorem hAC_eq_AQ_add_CQ : dist cfg.A cfg.C = dist cfg.A cfg.Q + dist cfg.C cfg.Q := by
  simpa [dist_comm, add_comm] using
    dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr cfg.Sbtw_AQC)

theorem hBC_eq_BD_add_CD : dist cfg.B cfg.C = dist cfg.B cfg.D + dist cfg.C cfg.D := by
  simpa [dist_comm, add_comm] using
    dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr cfg.Sbtw_BDC)

theorem hBM_eq : dist cfg.B cfg.M = dist cfg.A cfg.B - dist cfg.A cfg.M := by
  nlinarith [cfg.hAB_eq_AM_add_BM]

theorem hBN_eq : dist cfg.B cfg.N = dist cfg.A cfg.B - dist cfg.A cfg.N := by
  nlinarith [cfg.hAB_eq_AN_add_BN]

theorem hCP_eq : dist cfg.C cfg.P = dist cfg.A cfg.B - dist cfg.A cfg.P := by
  nlinarith [cfg.hAB_eq_AC, cfg.hAC_eq_AP_add_CP]

theorem hCQ_eq : dist cfg.C cfg.Q = dist cfg.A cfg.B - dist cfg.A cfg.Q := by
  nlinarith [cfg.hAB_eq_AC, cfg.hAC_eq_AQ_add_CQ]

theorem hCD_eq : dist cfg.C cfg.D = dist cfg.A cfg.B - dist cfg.B cfg.D := by
  nlinarith [cfg.hAB_eq_BC, cfg.hBC_eq_BD_add_CD]

/-! ### Final algebra -/

theorem hleft_scaled :
    dist cfg.A cfg.B * (dist cfg.A cfg.M + dist cfg.A cfg.N) =
      dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.A cfg.M * dist cfg.A cfg.N - dist cfg.B cfg.D * dist cfg.B cfg.D := by
  have h := cfg.hBD_sq_eq_BM_mul_BN
  rw [cfg.hBM_eq, cfg.hBN_eq] at h
  nlinarith [h]

theorem hright_scaled :
    dist cfg.A cfg.B * (dist cfg.A cfg.P + dist cfg.A cfg.Q) =
      dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.A cfg.P * dist cfg.A cfg.Q - dist cfg.C cfg.D * dist cfg.C cfg.D := by
  have h := cfg.hCD_sq_eq_CP_mul_CQ
  rw [cfg.hCP_eq, cfg.hCQ_eq] at h
  nlinarith [h]

theorem hBD_term_eq_CD_term :
    dist cfg.A cfg.B * dist cfg.B cfg.D - dist cfg.B cfg.D * dist cfg.B cfg.D =
      dist cfg.A cfg.B * dist cfg.C cfg.D - dist cfg.C cfg.D * dist cfg.C cfg.D := by
  rw [cfg.hCD_eq]
  ring

theorem hscaled :
    dist cfg.A cfg.B * (dist cfg.B cfg.D + dist cfg.A cfg.M + dist cfg.A cfg.N) =
      dist cfg.A cfg.B * (dist cfg.C cfg.D + dist cfg.A cfg.P + dist cfg.A cfg.Q) := by
  calc
    dist cfg.A cfg.B * (dist cfg.B cfg.D + dist cfg.A cfg.M + dist cfg.A cfg.N)
      = dist cfg.A cfg.B * dist cfg.B cfg.D + dist cfg.A cfg.B * (dist cfg.A cfg.M + dist cfg.A cfg.N) := by
          ring
    _ = dist cfg.A cfg.B * dist cfg.B cfg.D
        + (dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.A cfg.M * dist cfg.A cfg.N - dist cfg.B cfg.D * dist cfg.B cfg.D) := by
          rw [cfg.hleft_scaled]
    _ = dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.A cfg.M * dist cfg.A cfg.N
        + (dist cfg.A cfg.B * dist cfg.B cfg.D - dist cfg.B cfg.D * dist cfg.B cfg.D) := by
          ring
    _ = dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.A cfg.P * dist cfg.A cfg.Q
        + (dist cfg.A cfg.B * dist cfg.C cfg.D - dist cfg.C cfg.D * dist cfg.C cfg.D) := by
          rw [cfg.hAM_mul_AN_eq_AP_mul_AQ, cfg.hBD_term_eq_CD_term]
    _ = dist cfg.A cfg.B * dist cfg.C cfg.D
        + (dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.A cfg.P * dist cfg.A cfg.Q - dist cfg.C cfg.D * dist cfg.C cfg.D) := by
          ring
    _ = dist cfg.A cfg.B * dist cfg.C cfg.D + dist cfg.A cfg.B * (dist cfg.A cfg.P + dist cfg.A cfg.Q) := by
          rw [cfg.hright_scaled]
    _ = dist cfg.A cfg.B * (dist cfg.C cfg.D + dist cfg.A cfg.P + dist cfg.A cfg.Q) := by
          ring

theorem result : dist cfg.B cfg.D + dist cfg.A cfg.M + dist cfg.A cfg.N =
    dist cfg.C cfg.D + dist cfg.A cfg.P + dist cfg.A cfg.Q := by
  have hAB_ne_zero : dist cfg.A cfg.B ≠ 0 := dist_ne_zero.mpr cfg.A_ne_B
  apply (mul_right_cancel₀ hAB_ne_zero)
  simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
    using cfg.hscaled

end Cfg

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
  let cfg : Cfg (V := V) (Pt := Pt) :=
    ⟨A, B, C, D, M, N, P, Q, affineIndependent_ABC, triangle_ABC_def, equilateral_ABC,
      Sbtw_BDC, ω, ω_tangent_at_D, M_N_def, M_ne_N, Sbtw_AMB, Sbtw_ANB, P_Q_def, P_ne_Q,
      Sbtw_APC, Sbtw_AQC⟩
  simpa using cfg.result

end BMO2_2004P1
