/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Sphere.Power

set_option linter.unusedSectionVars false

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace
open InnerProductGeometry

namespace BMO2_2024P3

noncomputable section

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

structure Cfg where
  (A B C P X Y : Pt)
  (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
  {triangle_ABC : Triangle ℝ Pt}
  (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
  (acute_ABC : triangle_ABC.AcuteAngled)
  (AB_gt_AC : dist A B > dist A C)
  (P_def :
    triangle_ABC.circumsphere.IsTangentAt B line[ℝ, P, B] ∧
      triangle_ABC.circumsphere.IsTangentAt C line[ℝ, P, C])
  (X_def : X ∈ line[ℝ, A, B] ⊓ line[ℝ, midpoint ℝ P B, midpoint ℝ P C])
  (Y_def : Y ∈ line[ℝ, A, C] ⊓ line[ℝ, midpoint ℝ P B, midpoint ℝ P C])

namespace Cfg

variable (cfg : Cfg (V := V) (Pt := Pt))

theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

theorem hX_mem_AB : cfg.X ∈ line[ℝ, cfg.A, cfg.B] :=
  cfg.X_def.1

theorem hX_mem_midLine : cfg.X ∈ line[ℝ, midpoint ℝ cfg.P cfg.B, midpoint ℝ cfg.P cfg.C] :=
  cfg.X_def.2

theorem hY_mem_AC : cfg.Y ∈ line[ℝ, cfg.A, cfg.C] :=
  cfg.Y_def.1

theorem hY_mem_midLine : cfg.Y ∈ line[ℝ, midpoint ℝ cfg.P cfg.B, midpoint ℝ cfg.P cfg.C] :=
  cfg.Y_def.2

theorem exists_lineMap_AB : ∃ t : ℝ, AffineMap.lineMap cfg.A cfg.B t = cfg.X := by
  simpa using mem_affineSpan_pair_iff_exists_lineMap_eq.mp cfg.hX_mem_AB

theorem exists_lineMap_AC : ∃ t : ℝ, AffineMap.lineMap cfg.A cfg.C t = cfg.Y := by
  simpa using mem_affineSpan_pair_iff_exists_lineMap_eq.mp cfg.hY_mem_AC

theorem exists_lineMap_mid_X :
    ∃ t : ℝ,
      AffineMap.lineMap (midpoint ℝ cfg.P cfg.B) (midpoint ℝ cfg.P cfg.C) t = cfg.X := by
  simpa using mem_affineSpan_pair_iff_exists_lineMap_eq.mp cfg.hX_mem_midLine

theorem exists_lineMap_mid_Y :
    ∃ t : ℝ,
      AffineMap.lineMap (midpoint ℝ cfg.P cfg.B) (midpoint ℝ cfg.P cfg.C) t = cfg.Y := by
  simpa using mem_affineSpan_pair_iff_exists_lineMap_eq.mp cfg.hY_mem_midLine

theorem hPB_ortho :
    inner ℝ (cfg.P -ᵥ cfg.B : V) (cfg.B -ᵥ cfg.triangle_ABC.circumsphere.center : V) = 0 := by
  exact cfg.P_def.1.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ cfg.P cfg.B)

theorem hPC_ortho :
    inner ℝ (cfg.P -ᵥ cfg.C : V) (cfg.C -ᵥ cfg.triangle_ABC.circumsphere.center : V) = 0 := by
  exact cfg.P_def.2.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ cfg.P cfg.C)

theorem result : Cospherical {cfg.A, cfg.X, cfg.P, cfg.Y} := by
  obtain ⟨t, hX_t⟩ := cfg.exists_lineMap_AB
  obtain ⟨u, hX_u⟩ := cfg.exists_lineMap_mid_X
  let b : V := cfg.B -ᵥ cfg.A
  let c : V := cfg.C -ᵥ cfg.A
  let p : V := cfg.P -ᵥ cfg.A
  let o : V := cfg.triangle_ABC.circumsphere.center -ᵥ cfg.A
  have hlin : LinearIndependent ℝ ![b, c] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hnotcol : ¬ Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
      affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC
    have hb_ne : b ≠ 0 := by
      exact vsub_ne_zero.mpr cfg.A_ne_B.symm
    by_cases ht : t = 0
    · have hs : s = 0 := by
        have hs_or : s = 0 ∨ b = 0 := by
          apply smul_eq_zero.mp
          simpa [ht, b] using hst
        exact hs_or.resolve_right hb_ne
      exact ⟨hs, ht⟩
    · have hc_mem : cfg.C ∈ line[ℝ, cfg.A, cfg.B] := by
        have hc_eq : cfg.C = (-s / t) • (cfg.B -ᵥ cfg.A) +ᵥ cfg.A := by
          refine (eq_vadd_iff_vsub_eq cfg.C cfg.A ((-s / t) • b)).mpr ?_
          have htc : t • c = -s • b := by
            nlinarith [hst]
          calc
            c = t⁻¹ • (t • c) := by simp [ht]
            _ = t⁻¹ • (-s • b) := by rw [htc]
            _ = (-s / t) • b := by field_simp [div_eq_mul_inv]
        rw [hc_eq]
        exact smul_vsub_vadd_mem_affineSpan_pair (-s / t) cfg.A cfg.B
      have hcol : Collinear ℝ ({cfg.C, cfg.A, cfg.B} : Set Pt) :=
        collinear_insert_of_mem_affineSpan_pair (p₁ := cfg.C) (p₂ := cfg.A) (p₃ := cfg.B) hc_mem
      have hcol' : Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) := by
        simpa [Set.insert_comm, Set.pair_comm, Set.insert_left_comm] using hcol
      exact (hnotcol hcol').elim
  have hspan : Submodule.span ℝ (Set.range ![b, c]) = ⊤ := by
    exact hlin.span_eq_top_of_card_eq_finrank (by simpa using (Fact.out : finrank ℝ V = 2).symm)
  let basis : Basis (Fin 2) ℝ V := Basis.mk hlin hspan.ge
  let α : ℝ := basis.coord 0 p
  let β : ℝ := basis.coord 1 p
  have hp_eq : p = α • b + β • c := by
    simpa [basis, α, β, Fin.sum_univ_two] using (basis.sum_repr p).symm
  have hx_coeff :
      t • b = ((α + 1 - u) / 2 : ℝ) • b + ((β + u) / 2 : ℝ) • c := by
    have hXt_vsub : cfg.X -ᵥ cfg.A = t • b := by
      simpa [hX_t, b] using AffineMap.lineMap_vsub_left cfg.A cfg.B t
    have hNminusM : midpoint ℝ cfg.P cfg.C -ᵥ midpoint ℝ cfg.P cfg.B = (1 / 2 : ℝ) • (c - b) := by
      simpa [b, c, sub_eq_add_neg] using midpoint_vsub_midpoint_same_left (R := ℝ) cfg.P cfg.C cfg.B
    have hMminusA : midpoint ℝ cfg.P cfg.B -ᵥ cfg.A = (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • b := by
      simpa [b, p] using midpoint_vsub (R := ℝ) cfg.P cfg.B cfg.A
    have hXu_vsub : cfg.X -ᵥ cfg.A = ((α + 1 - u) / 2 : ℝ) • b + ((β + u) / 2 : ℝ) • c := by
      rw [← hX_u, AffineMap.lineMap_apply, vadd_vsub_assoc, hNminusM, hMminusA, hp_eq]
      ring
    exact hXt_vsub.symm.trans hXu_vsub
  have ht_eq : t = (α + 1 - u) / 2 := by
    have hx_coeff' : (t : ℝ) • b + (0 : ℝ) • c = ((α + 1 - u) / 2 : ℝ) • b + ((β + u) / 2 : ℝ) • c := by
      simpa using hx_coeff
    have ⟨heq_t, _⟩ := hlin.eq_of_pair hx_coeff'
    exact heq_t
  have hβu_eq : 0 = (β + u) / 2 := by
    have hx_coeff' : (t : ℝ) • b + (0 : ℝ) • c = ((α + 1 - u) / 2 : ℝ) • b + ((β + u) / 2 : ℝ) • c := by
      simpa using hx_coeff
    have ⟨_, heq_c⟩ := hlin.eq_of_pair hx_coeff'
    exact heq_c
  have ht_sum : 2 * t = α + β + 1 := by
    nlinarith [ht_eq, hβu_eq]
  have hA_mem : cfg.A ∈ cfg.triangle_ABC.circumsphere := by
    simpa [cfg.triangle_ABC_def] using cfg.triangle_ABC.mem_circumsphere (i := 0)
  have hB_mem : cfg.B ∈ cfg.triangle_ABC.circumsphere := by
    simpa [cfg.triangle_ABC_def] using cfg.triangle_ABC.mem_circumsphere (i := 1)
  have hC_mem : cfg.C ∈ cfg.triangle_ABC.circumsphere := by
    simpa [cfg.triangle_ABC_def] using cfg.triangle_ABC.mem_circumsphere (i := 2)
  have hdist_BO : dist cfg.B cfg.triangle_ABC.circumsphere.center =
      dist cfg.A cfg.triangle_ABC.circumsphere.center := by
    calc
      dist cfg.B cfg.triangle_ABC.circumsphere.center = cfg.triangle_ABC.circumsphere.radius := by
        simpa [mem_sphere] using hB_mem
      _ = dist cfg.A cfg.triangle_ABC.circumsphere.center := by
        symm
        simpa [mem_sphere] using hA_mem
  have hdist_CO : dist cfg.C cfg.triangle_ABC.circumsphere.center =
      dist cfg.A cfg.triangle_ABC.circumsphere.center := by
    calc
      dist cfg.C cfg.triangle_ABC.circumsphere.center = cfg.triangle_ABC.circumsphere.radius := by
        simpa [mem_sphere] using hC_mem
      _ = dist cfg.A cfg.triangle_ABC.circumsphere.center := by
        symm
        simpa [mem_sphere] using hA_mem
  have hb_sq : ‖b - o‖ ^ 2 = ‖o‖ ^ 2 := by
    have hsq := congrArg (fun r => r ^ 2) hdist_BO
    simp only [dist_eq_norm_vsub V cfg.B, dist_eq_norm_vsub V cfg.A] at hsq
    convert hsq using 2 <;> simp [b, o, vsub_eq_sub]
  have hc_sq : ‖c - o‖ ^ 2 = ‖o‖ ^ 2 := by
    have hsq := congrArg (fun r => r ^ 2) hdist_CO
    simp only [dist_eq_norm_vsub V cfg.C, dist_eq_norm_vsub V cfg.A] at hsq
    convert hsq using 2 <;> simp [c, o, vsub_eq_sub]
  have hbo : 2 * inner ℝ (o : V) (b : V) = ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real] at hb_sq
    nlinarith
  have hco : 2 * inner ℝ (o : V) (c : V) = ‖c‖ ^ 2 := by
    rw [norm_sub_sq_real] at hc_sq
    nlinarith
  have hpb_eq : inner ℝ (p : V) (b : V) - inner ℝ (p : V) (o : V) = ‖b‖ ^ 2 / 2 := by
    have h := Cfg.hPB_ortho cfg
    rw [show cfg.P -ᵥ cfg.B = p - b by simp [p, b, vsub_eq_sub],
      show cfg.B -ᵥ cfg.triangle_ABC.circumsphere.center = b - o by
        simp [b, o, vsub_eq_sub], inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm o b] at h
    nlinarith [hbo, h]
  have hpc_eq : inner ℝ (p : V) (c : V) - inner ℝ (p : V) (o : V) = ‖c‖ ^ 2 / 2 := by
    have h := Cfg.hPC_ortho cfg
    rw [show cfg.P -ᵥ cfg.C = p - c by simp [p, c, vsub_eq_sub],
      show cfg.C -ᵥ cfg.triangle_ABC.circumsphere.center = c - o by
        simp [c, o, vsub_eq_sub], inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm o c] at h
    nlinarith [hco, h]
  have hp_norm_inner : ‖p‖ ^ 2 = α * inner ℝ (p : V) (b : V) + β * inner ℝ (p : V) (c : V) := by
    rw [← real_inner_self_eq_norm_sq, hp_eq, inner_add_right, inner_smul_right]
  have hpo : 2 * inner ℝ (p : V) (o : V) = α * ‖b‖ ^ 2 + β * ‖c‖ ^ 2 := by
    rw [hp_eq, inner_add_left, inner_smul_left, real_inner_comm b o, real_inner_comm c o]
    nlinarith [hbo, hco]
  have hp_sq : ‖p‖ ^ 2 = t * (α * ‖b‖ ^ 2 + β * ‖c‖ ^ 2) := by
    nlinarith [hp_norm_inner, hpb_eq, hpc_eq, ht_sum]
  have hp_sq' : ‖p‖ ^ 2 = 2 * t * inner ℝ (p : V) (o : V) := by
    nlinarith [hp_sq, hpo]
  let center : Pt := AffineMap.lineMap cfg.A cfg.triangle_ABC.circumsphere.center t
  let s : Sphere Pt := ⟨center, dist cfg.A center⟩
  have hA_mem_s : cfg.A ∈ s := by
    simp [s, center, mem_sphere]
  have hX_mem_s : cfg.X ∈ s := by
    have hsq : dist cfg.X center ^ 2 = dist cfg.A center ^ 2 := by
      rw [hX_t, center, dist_eq_norm_vsub V, dist_eq_norm_vsub V,
        AffineMap.lineMap_vsub_lineMap, AffineMap.lineMap_apply_module,
        AffineMap.lineMap_vsub_left]
      simp [hb_sq, b, o, norm_smul]
    have hdist : dist cfg.X center = dist cfg.A center := by
      nlinarith [hsq, dist_nonneg, show 0 ≤ dist cfg.A center from dist_nonneg]
    simpa [s, mem_sphere] using hdist
  have hY_mem_s : cfg.Y ∈ s := by
    obtain ⟨tY, hY_t⟩ := cfg.exists_lineMap_AC
    have hy_coeff :
        tY • c = ((α + 1 - u) / 2 : ℝ) • b + ((β + u) / 2 : ℝ) • c := by
      calc
        tY • c = cfg.Y -ᵥ cfg.A := by simpa [hY_t, c] using (AffineMap.lineMap_vsub_left cfg.A cfg.C tY).symm
        _ = AffineMap.lineMap (midpoint ℝ cfg.P cfg.B) (midpoint ℝ cfg.P cfg.C) u -ᵥ cfg.A := by
              rw [cfg.hY_mem_midLine]
              exact rfl
        _ = u • ((midpoint ℝ cfg.P cfg.C) -ᵥ midpoint ℝ cfg.P cfg.B)
              + (midpoint ℝ cfg.P cfg.B -ᵥ cfg.A) := by
              rw [AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub]
        _ = u • ((1 / 2 : ℝ) • (c - b)) + ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • b) := by
              simp [b, c, p, midpoint_vsub_midpoint_same_left, midpoint_vsub]
        _ = ((α + 1 - u) / 2 : ℝ) • b + ((β + u) / 2 : ℝ) • c := by
              rw [hp_eq]
              ring_nf
    have htY : tY = t := by
      have hpair := hlin.eq_of_pair (by simpa [add_comm] using hy_coeff)
      nlinarith [hpair.1, hpair.2, ht_eq, hβu_eq]
    have hsq : dist cfg.Y center ^ 2 = dist cfg.A center ^ 2 := by
      rw [hY_t, htY, center, dist_eq_norm_vsub V, dist_eq_norm_vsub V,
        AffineMap.lineMap_vsub_lineMap, AffineMap.lineMap_apply_module,
        AffineMap.lineMap_vsub_left]
      simp [hc_sq, c, o, norm_smul]
    have hdist : dist cfg.Y center = dist cfg.A center := by
      nlinarith [hsq, dist_nonneg, show 0 ≤ dist cfg.A center from dist_nonneg]
    simpa [s, mem_sphere] using hdist
  have hP_mem_s : cfg.P ∈ s := by
    have hsq : dist cfg.P center ^ 2 = dist cfg.A center ^ 2 := by
      rw [center, dist_eq_norm_vsub V, dist_eq_norm_vsub V,
        show cfg.P -ᵥ AffineMap.lineMap cfg.A cfg.triangle_ABC.circumsphere.center t = p - t • o by
          rw [show AffineMap.lineMap cfg.A cfg.triangle_ABC.circumsphere.center t -ᵥ cfg.A = t • o by
            simpa [o] using AffineMap.lineMap_vsub_left cfg.A cfg.triangle_ABC.circumsphere.center t,
            ← vsub_eq_sub, vsub_assoc],
        show cfg.A -ᵥ AffineMap.lineMap cfg.A cfg.triangle_ABC.circumsphere.center t = -t • o by
          simpa [o] using AffineMap.left_vsub_lineMap cfg.A cfg.triangle_ABC.circumsphere.center t]
      rw [norm_sub_sq_real]
      have ho_sq : ‖t • o‖ ^ 2 = t ^ 2 * ‖o‖ ^ 2 := by simp [norm_smul]
      nlinarith [hp_sq', ho_sq]
    have hdist : dist cfg.P center = dist cfg.A center := by
      nlinarith [hsq, dist_nonneg, show 0 ≤ dist cfg.A center from dist_nonneg]
    simpa [s, mem_sphere] using hdist
  rw [cospherical_iff_exists_sphere]
  refine ⟨s, ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hA_mem_s
  · exact hX_mem_s
  · exact hP_mem_s
  · exact hY_mem_s

end Cfg

/-- BMO Round 2 2024 Problem 3.
 Let 𝐴𝐵𝐶 be an acute-angled triangle with 𝐴𝐵 > 𝐴𝐶. Let 𝑃 be the intersection of the
tangents to the circumcircle of 𝐴𝐵𝐶 at 𝐵 and 𝐶. The line through the midpoints of line
segments 𝑃𝐵 and 𝑃𝐶 meets lines 𝐴𝐵 and 𝐴𝐶 at 𝑋 and 𝑌 respectively.
Prove that the quadrilateral 𝐴𝑋𝑃𝑌 is cyclic. -/
theorem result {A B C P X Y : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (acute_ABC : triangle_ABC.AcuteAngled)
    (AB_gt_AC : dist A B > dist A C)
    (P_def :
      triangle_ABC.circumsphere.IsTangentAt B line[ℝ, P, B] ∧
        triangle_ABC.circumsphere.IsTangentAt C line[ℝ, P, C])
    (X_def : X ∈ line[ℝ, A, B] ⊓ line[ℝ, midpoint ℝ P B, midpoint ℝ P C])
    (Y_def : Y ∈ line[ℝ, A, C] ⊓ line[ℝ, midpoint ℝ P B, midpoint ℝ P C]) :
    Cospherical {A, X, P, Y} := by
  let cfg : Cfg (V := V) (Pt := Pt) :=
    ⟨A, B, C, P, X, Y, affineIndependent_ABC, triangle_ABC_def, acute_ABC, AB_gt_AC,
      P_def, X_def, Y_def⟩
  simpa using cfg.result

end

end BMO2_2024P3
