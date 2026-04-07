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
  have hAB_eq_AC : dist A B = dist A C := by
    simpa [triangle_ABC_def] using
      equilateral_ABC.dist_eq (i₁ := (0 : Fin 3)) (i₂ := 1) (i₃ := 0) (i₄ := 2)
        (by decide) (by decide)
  have hAB_eq_BC : dist A B = dist B C := by
    simpa [triangle_ABC_def] using
      equilateral_ABC.dist_eq (i₁ := (0 : Fin 3)) (i₂ := 1) (i₃ := 1) (i₄ := 2)
        (by decide) (by decide)
  have hM_mem : M ∈ (ω : Set Pt) ∩ line[ℝ, A, B] := by
    have h : M ∈ ({M, N} : Set Pt) := by simp
    simpa [M_N_def] using h
  have hN_mem : N ∈ (ω : Set Pt) ∩ line[ℝ, A, B] := by
    have h : N ∈ ({M, N} : Set Pt) := by simp
    simpa [M_N_def] using h
  have hP_mem : P ∈ (ω : Set Pt) ∩ line[ℝ, A, C] := by
    have h : P ∈ ({P, Q} : Set Pt) := by simp
    simpa [P_Q_def] using h
  have hQ_mem : Q ∈ (ω : Set Pt) ∩ line[ℝ, A, C] := by
    have h : Q ∈ ({P, Q} : Set Pt) := by simp
    simpa [P_Q_def] using h
  have hMN_eq_lineAB : line[ℝ, M, N] = line[ℝ, A, B] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hM_mem.2 hN_mem.2 M_ne_N
  have hPQ_eq_lineAC : line[ℝ, P, Q] = line[ℝ, A, C] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hP_mem.2 hQ_mem.2 P_ne_Q
  have hA_mem_lineMN : A ∈ line[ℝ, M, N] := by
    rw [hMN_eq_lineAB]
    exact left_mem_affineSpan_pair ℝ A B
  have hB_mem_lineMN : B ∈ line[ℝ, M, N] := by
    rw [hMN_eq_lineAB]
    exact right_mem_affineSpan_pair ℝ A B
  have hA_mem_linePQ : A ∈ line[ℝ, P, Q] := by
    rw [hPQ_eq_lineAC]
    exact left_mem_affineSpan_pair ℝ A C
  have hC_mem_linePQ : C ∈ line[ℝ, P, Q] := by
    rw [hPQ_eq_lineAC]
    exact right_mem_affineSpan_pair ℝ A C
  have hBD_eq_lineBC : line[ℝ, B, D] = line[ℝ, B, C] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (left_mem_affineSpan_pair ℝ B C) Sbtw_BDC.wbtw.mem_affineSpan Sbtw_BDC.left_ne
  have hCD_eq_lineBC : line[ℝ, C, D] = line[ℝ, B, C] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (right_mem_affineSpan_pair ℝ B C) Sbtw_BDC.wbtw.mem_affineSpan Sbtw_BDC.right_ne
  have hω_tangent_BD : ω.IsTangentAt D line[ℝ, B, D] := by
    rwa [hBD_eq_lineBC]
  have hω_tangent_CD : ω.IsTangentAt D line[ℝ, C, D] := by
    rwa [hCD_eq_lineBC]
  have hAM_mul_AN_eq_AP_mul_AQ : dist A M * dist A N = dist A P * dist A Q := by
    calc
      dist A M * dist A N = |ω.power A| :=
        ω.mul_dist_eq_abs_power hA_mem_lineMN hM_mem.1 hN_mem.1
      _ = dist A P * dist A Q := by
        symm
        exact ω.mul_dist_eq_abs_power hA_mem_linePQ hP_mem.1 hQ_mem.1
  have hBD_sq_eq_BM_mul_BN : dist B D * dist B D = dist B M * dist B N := by
    simpa [pow_two] using
      Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant hM_mem.1 hN_mem.1 hB_mem_lineMN hω_tangent_BD
  have hCD_sq_eq_CP_mul_CQ : dist C D * dist C D = dist C P * dist C Q := by
    simpa [pow_two] using
      Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant hP_mem.1 hQ_mem.1 hC_mem_linePQ hω_tangent_CD
  have hAB_eq_AM_add_BM : dist A B = dist A M + dist B M := by
    simpa [dist_comm, add_comm] using
      dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr Sbtw_AMB)
  have hAB_eq_AN_add_BN : dist A B = dist A N + dist B N := by
    simpa [dist_comm, add_comm] using
      dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr Sbtw_ANB)
  have hAC_eq_AP_add_CP : dist A C = dist A P + dist C P := by
    simpa [dist_comm, add_comm] using
      dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr Sbtw_APC)
  have hAC_eq_AQ_add_CQ : dist A C = dist A Q + dist C Q := by
    simpa [dist_comm, add_comm] using
      dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr Sbtw_AQC)
  have hBC_eq_BD_add_CD : dist B C = dist B D + dist C D := by
    simpa [dist_comm, add_comm] using
      dist_eq_add_dist_of_angle_eq_pi (angle_eq_pi_iff_sbtw.mpr Sbtw_BDC)
  have hBM_eq : dist B M = dist A B - dist A M := by
    nlinarith [hAB_eq_AM_add_BM]
  have hBN_eq : dist B N = dist A B - dist A N := by
    nlinarith [hAB_eq_AN_add_BN]
  have hCP_eq : dist C P = dist A B - dist A P := by
    nlinarith [hAB_eq_AC, hAC_eq_AP_add_CP]
  have hCQ_eq : dist C Q = dist A B - dist A Q := by
    nlinarith [hAB_eq_AC, hAC_eq_AQ_add_CQ]
  have hCD_eq : dist C D = dist A B - dist B D := by
    nlinarith [hAB_eq_BC, hBC_eq_BD_add_CD]
  have hleft_scaled :
      dist A B * (dist A M + dist A N) =
        dist A B * dist A B + dist A M * dist A N - dist B D * dist B D := by
    have h := hBD_sq_eq_BM_mul_BN
    rw [hBM_eq, hBN_eq] at h
    nlinarith [h]
  have hright_scaled :
      dist A B * (dist A P + dist A Q) =
        dist A B * dist A B + dist A P * dist A Q - dist C D * dist C D := by
    have h := hCD_sq_eq_CP_mul_CQ
    rw [hCP_eq, hCQ_eq] at h
    nlinarith [h]
  have hBD_term_eq_CD_term :
      dist A B * dist B D - dist B D * dist B D =
        dist A B * dist C D - dist C D * dist C D := by
    rw [hCD_eq]
    ring
  have hscaled :
      dist A B * (dist B D + dist A M + dist A N) =
        dist A B * (dist C D + dist A P + dist A Q) := by
    calc
      dist A B * (dist B D + dist A M + dist A N)
      = dist A B * dist B D + dist A B * (dist A M + dist A N) := by
          ring
        _ = dist A B * dist B D
          + (dist A B * dist A B + dist A M * dist A N - dist B D * dist B D) := by
          rw [hleft_scaled]
        _ = dist A B * dist A B + dist A M * dist A N
          + (dist A B * dist B D - dist B D * dist B D) := by
          ring
        _ = dist A B * dist A B + dist A P * dist A Q
          + (dist A B * dist C D - dist C D * dist C D) := by
          rw [hAM_mul_AN_eq_AP_mul_AQ, hBD_term_eq_CD_term]
        _ = dist A B * dist C D
          + (dist A B * dist A B + dist A P * dist A Q - dist C D * dist C D) := by
          ring
        _ = dist A B * dist C D + dist A B * (dist A P + dist A Q) := by
          rw [hright_scaled]
        _ = dist A B * (dist C D + dist A P + dist A Q) := by
          ring
  have hAB_ne : A ≠ B := affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hAB_ne_zero : dist A B ≠ 0 := dist_ne_zero.mpr hAB_ne
  apply (mul_right_cancel₀ hAB_ne_zero)
  simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
    using hscaled

end BMO2_2004P1
