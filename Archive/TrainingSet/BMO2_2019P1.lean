/-
Copyright (c) 2026 Zheng Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Chu
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.PerpBisector

open scoped Real
open Affine EuclideanGeometry Module
open AffineSubspace

namespace BMO2_2019P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- BMO Round 2 2019 Problem 1.
Let ABC be a triangle. Let L be the line through B perpendicular to
AB. The perpendicular from A to BC meets L at the point D. The
perpendicular bisector of BC meets L at the point P. Let E be the foot
of the perpendicular from D to AC.
Prove that triangle BPE is isosceles.
-/

theorem result {A B C L D P E : Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affineIndependent_ABC⟩)
    (L_perp : line[ℝ, A, B].direction ⟂ line[ℝ, B, L].direction)
    (AD_perp : line[ℝ, A, D].direction ⟂ line[ℝ, B, C].direction)
    (D_def : D ∈ line[ℝ, A, D] ⊓ line[ℝ, B, L])
    (P_def : P ∈ (perpBisector B C) ⊓ line[ℝ, B, L])
    (E_def : E = orthogonalProjection (line[ℝ, A, C]) D) :
    dist P B = dist P E := by
  classical
  have hAB : A ≠ B := by
    intro h
    have hcol : Collinear ℝ ({A, B, C} : Set Pt) := by
      rw [h]
      exact collinear_pair ℝ B C
    exact (affineIndependent_iff_not_collinear_set.mp affineIndependent_ABC) hcol
  have hBC : B ≠ C := by
    intro h
    have hcol : Collinear ℝ ({A, B, C} : Set Pt) := by
      rw [h]
      exact collinear_pair ℝ A B
    exact (affineIndependent_iff_not_collinear_set.mp affineIndependent_ABC) hcol

  let a : ℝ := dist A B
  have ha : 0 < a := by
    dsimp [a]
    exact dist_pos.mpr hAB

  let f : Fin 2 → V := ![A -ᵥ B, C -ᵥ B]
  let b : OrthonormalBasis (Fin 2) ℝ V :=
    gramSchmidtOrthonormalBasis (by simpa using (show finrank ℝ V = 2 from (Fact.out : finrank ℝ V = 2))) f

  have hb0 : b 0 = (a⁻¹ : ℝ) • (A -ᵥ B) := by
    have hf0 : f 0 ≠ 0 := by
      simp [f, hAB]
    have hb0' : b 0 = gramSchmidtNormed ℝ f 0 := by
      simpa using (gramSchmidtOrthonormalBasis_apply
        (h := by simpa using (show finrank ℝ V = 2 from (Fact.out : finrank ℝ V = 2)))
        (f := f) (i := (0 : Fin 2)) (by
          simpa [f, gramSchmidtNormed, gramSchmidt_bot] using hf0))
    simp [b, a, f, gramSchmidtNormed, gramSchmidt_bot, dist_eq_norm_vsub, hb0', ha.ne']

  let x : ℝ := ⟪b 0, C -ᵥ B⟫
  let y : ℝ := ⟪b 1, C -ᵥ B⟫
  let d : ℝ := ⟪b 1, D -ᵥ B⟫
  let p : ℝ := ⟪b 1, P -ᵥ B⟫

  have hA : A -ᵥ B = a • b 0 := by
    rw [hb0]
    simp [a, ha.ne']

  have hC : C -ᵥ B = x • b 0 + y • b 1 := by
    have := b.sum_repr (C -ᵥ B)
    simp [x, y] at this
    simpa [x, y] using this

  have hD0 : ⟪b 0, D -ᵥ B⟫ = 0 := by
    have hDirBD : D -ᵥ B ∈ line[ℝ, B, L].direction := by
      exact vsub_mem_direction (by simpa using (D_def.2.2 : D ∈ line[ℝ, B, L])) (by simp)
    have hDirAB : b 0 ∈ line[ℝ, A, B].direction := by
      rw [hA]
      exact line[ℝ, A, B].direction.smul_mem a (vsub_mem_direction (by simp) (by simp))
    exact L_perp.inner_eq hDirAB hDirBD

  have hD : D -ᵥ B = d • b 1 := by
    have := b.sum_repr (D -ᵥ B)
    simp [d, hD0] at this
    simpa [d, hD0] using this

  have hP0 : ⟪b 0, P -ᵥ B⟫ = 0 := by
    have hDirPB : P -ᵥ B ∈ line[ℝ, B, L].direction := by
      exact vsub_mem_direction (by simpa using (P_def.2.2 : P ∈ line[ℝ, B, L])) (by simp)
    have hDirAB : b 0 ∈ line[ℝ, A, B].direction := by
      rw [hA]
      exact line[ℝ, A, B].direction.smul_mem a (vsub_mem_direction (by simp) (by simp))
    exact L_perp.inner_eq hDirAB hDirPB

  have hP : P -ᵥ B = p • b 1 := by
    have := b.sum_repr (P -ᵥ B)
    simp [p, hP0] at this
    simpa [p, hP0] using this

  have hPBPC : dist P B = dist P C := by
    exact (mem_perpBisector_iff_dist_eq).1 P_def.1

  have hBis : 2 * p * y = x ^ 2 + y ^ 2 := by
    have h1 : dist P B ^ 2 = p ^ 2 := by
      rw [dist_eq_norm_vsub, hP]
      simp [sq]
    have h2 : dist P C ^ 2 = x ^ 2 + (y - p) ^ 2 := by
      rw [dist_eq_norm_vsub, hP, hC]
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero]
      · simp [sq]
      · simpa using (b.orthonormal.2 (by decide : (0 : Fin 2) ≠ 1))
    nlinarith [hPBPC, h1, h2]

  have hADorth : ⟪A -ᵥ D, C -ᵥ B⟫ = 0 := by
    exact AD_perp.inner_eq
      (vsub_mem_direction (by simpa using (D_def.1 : D ∈ line[ℝ, A, D])) (by simp))
      (vsub_mem_direction (by simp) (by simp))

  have hAlt : a * x = d * y := by
    have h : ⟪a • b 0 - d • b 1, x • b 0 + y • b 1⟫ = 0 := by
      rw [← hA, ← hC, ← hD]
      simpa [x, y, d, hA, hC, hD, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
        using hADorth
    nlinarith [h]

  obtain ⟨s, rfl⟩ := (AffineSubspace.mem_affineSpan_pair_iff_exists_lineMap_eq
    (p := E) (p₁ := A) (p₂ := C)).1 (by
      simpa [E_def] using (orthogonalProjection_mem (s := line[ℝ, A, C]) D))

  have hEproj : ⟪D -ᵥ E, C -ᵥ A⟫ = 0 := by
    simpa [E_def] using
      (orthogonalProjection_vsub_mem_direction_orthogonal (s := line[ℝ, A, C]) D)

  have hE : E -ᵥ B = (a + s * (x - a)) • b 0 + (s * y) • b 1 := by
    rw [AffineMap.lineMap_vsub]
    simp [hA, hC, lineMap_apply_module, a, x, y, mul_add, add_mul, add_assoc, add_comm,
      add_left_comm, mul_assoc, mul_comm, mul_left_comm]

  have hProjEq : s * ((x - a) ^ 2 + y ^ 2) = a ^ 2 := by
    have h : ⟪D -ᵥ E, C -ᵥ A⟫ =
        - (a + s * (x - a)) * (x - a) + (d - s * y) * y := by
      rw [hE, hA, hC, hD]
      simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right]
    nlinarith [hEproj, hAlt, h]

  have hPBsq : dist P B ^ 2 = p ^ 2 := by
    rw [dist_eq_norm_vsub, hP]
    simp [sq]

  have hPEsq : dist P E ^ 2 = (a + s * (x - a)) ^ 2 + (s * y - p) ^ 2 := by
    rw [dist_eq_norm_vsub]
    rw [hE, hP]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero]
    · simp [sq]
    · simp [inner_smul_left, inner_smul_right, b.orthonormal.2 (by decide : (0 : Fin 2) ≠ 1)]

  have hfinal : dist P B ^ 2 = dist P E ^ 2 := by
    nlinarith [hBis, hProjEq, hPBsq, hPEsq]

  exact sq_eq_sq_iff_eq_or_eq_neg.mp hfinal |>.resolve_right (by positivity)

end BMO2_2019P1
