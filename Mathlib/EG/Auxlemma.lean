/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Geometry.Euclidean.Sphere.OrthRadius

noncomputable section

open scoped InnerProductSpace

/-! ## From `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`

The theorem `mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero` is placed in the
`Submodule` namespace with `open Module` to bring `finrank` into scope, matching
the original file structure.
-/

namespace Submodule

open Module

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

/-- If two nonzero vectors `w` and `u` are both orthogonal to the same nonzero vector `v`
in a two-dimensional inner product space, then `u` lies in the span of `w`. -/
theorem mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fact (finrank 𝕜 E = 2)] {u v w : E}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪v, u⟫_𝕜 = 0) (hwv : ⟪v, w⟫_𝕜 = 0) :
    u ∈ Submodule.span 𝕜 {w} := by
  haveI : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ 1
  have heq : 𝕜 ∙ w = (𝕜 ∙ v)ᗮ :=
      Submodule.eq_of_le_of_finrank_le
        ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hwv))
        (by rw [finrank_orthogonal_span_singleton (n := 1) hv, finrank_span_singleton hw])
  rwa [heq, Submodule.mem_orthogonal_singleton_iff_inner_right]

end Submodule

/-! ## From `Mathlib.Analysis.InnerProductSpace.Basic`

Helper lemmas `inner_eq_zero_of_left` / `inner_eq_zero_of_right` may also be from the
same PR. If they already exist in your Mathlib, remove them to avoid duplicates.
-/

section InnerProductBasicHelpers

variable {𝕜' E' : Type*} [RCLike 𝕜'] [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜' E']

end InnerProductBasicHelpers

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Subtracting the orthogonal projection of `u` onto `d` yields a vector orthogonal to `d`. -/
theorem real_inner_sub_smul_div_inner_self_eq_zero (u d : F) :
    ⟪u - (⟪u, d⟫_ℝ / ⟪d, d⟫_ℝ) • d, d⟫_ℝ = 0 := by
  rw [inner_sub_left, real_inner_smul_left]
  by_cases hd : ⟪d, d⟫_ℝ = 0
  · have : ‖d‖ = 0 := by rwa [real_inner_self_eq_norm_sq, sq_eq_zero_iff] at hd
    simp [inner_eq_zero_of_right u this]
  · field_simp; ring

/-! ## From `Mathlib.Geometry.Euclidean.Sphere.Basic`

These theorems live in the `EuclideanGeometry` namespace. The sphere type here is
`EuclideanGeometry.Sphere P` (not `Metric.Sphere`). Inner products use the unsubscripted
notation `⟪x, y⟫` via `open RealInnerProductSpace`.
-/

namespace EuclideanGeometry

open RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- Given two distinct points on a sphere, the inner product of the chord with
the radius vector at one endpoint is negative. -/
theorem inner_vsub_vsub_center_lt_zero {A B : P} {s : Sphere P}
    (hA : A ∈ s) (hB : B ∈ s) (hBA : B ≠ A) :
    ⟪B -ᵥ A, A -ᵥ s.center⟫ < 0 := by
  have hA' : ‖A -ᵥ s.center‖ = s.radius := by rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hA
  have hB' : ‖B -ᵥ s.center‖ = s.radius := by rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hB
  have hd : ‖B -ᵥ s.center‖ ^ 2 =
      ‖B -ᵥ A‖ ^ 2 + 2 * ⟪B -ᵥ A, A -ᵥ s.center⟫ + ‖A -ᵥ s.center‖ ^ 2 := by
    rw [← vsub_add_vsub_cancel B A s.center, norm_add_sq_real]
  rw [hB', hA'] at hd
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hBA))]

/-! ## From `Mathlib.Geometry.Euclidean.Sphere.OrthRadius`

If your Mathlib does NOT yet have the OrthRadius file at all, you will need to uncomment
the `orthRadius` block below. If it already exists, just keep the `lineOrOrthRadius` section.
-/

namespace Sphere

open AffineSubspace RealInnerProductSpace
open scoped Affine

/-
-- UNCOMMENT THIS BLOCK if `orthRadius` does not exist in your Mathlib:

/-- The affine subspace orthogonal to the radius vector of the sphere `s` at the point `p`. -/
noncomputable def orthRadius (s : Sphere P) (p : P) : AffineSubspace ℝ P :=
  .mk' p (ℝ ∙ (p -ᵥ s.center))ᗮ

lemma self_mem_orthRadius (s : Sphere P) (p : P) : p ∈ s.orthRadius p :=
  self_mem_mk' _ _

lemma mem_orthRadius_iff_inner_left {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 := by
  rw [orthRadius, mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_left]

lemma mem_orthRadius_iff_inner_right {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 := by
  rw [mem_orthRadius_iff_inner_left, inner_eq_zero_symm]
-/

variable {s : Sphere P} {p q : P}

open Classical in
/-- The line through two points on a sphere, or the orthogonal radius (tangent) at that point
when they coincide. -/
noncomputable def lineOrOrthRadius (s : Sphere P) (p q : P) : AffineSubspace ℝ P :=
  if p = q then s.orthRadius p else line[ℝ, p, q]

@[simp]
lemma lineOrOrthRadius_of_eq (h : p = q) : s.lineOrOrthRadius p q = s.orthRadius p := by
  rw [lineOrOrthRadius, if_pos h]

@[simp]
lemma lineOrOrthRadius_of_ne (h : p ≠ q) : s.lineOrOrthRadius p q = line[ℝ, p, q] := by
  rw [lineOrOrthRadius, if_neg h]

lemma left_mem_lineOrOrthRadius : p ∈ s.lineOrOrthRadius p q := by
  by_cases h : p = q <;> simp [lineOrOrthRadius, h, self_mem_orthRadius, left_mem_affineSpan_pair]

lemma right_mem_lineOrOrthRadius : q ∈ s.lineOrOrthRadius p q := by
  by_cases h : p = q <;> simp [lineOrOrthRadius, h, self_mem_orthRadius, right_mem_affineSpan_pair]

lemma lineOrOrthRadius_comm : s.lineOrOrthRadius p q = s.lineOrOrthRadius q p := by
  by_cases h : p = q <;> simp [lineOrOrthRadius, h, Ne.symm, affineSpan_pair_comm]

/-- A point on the sphere, distinct from both endpoints,
    cannot lie on the lineOrOrthRadius between them. -/
lemma not_mem_lineOrOrthRadius_of_mem_sphere {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C) :
    B ∉ s.lineOrOrthRadius A C := by
  by_cases hAC : A = C
  · subst hAC
    simp only [lineOrOrthRadius_of_eq, mem_orthRadius_iff_inner_left]
    intro h
    have := inner_pos_or_eq_of_dist_le_radius hA (mem_sphere.mp hB).le
    rw [← neg_vsub_eq_vsub_rev, inner_neg_left, h, neg_zero, lt_self_iff_false, false_or] at this
    exact hBA this.symm
  · simp only [lineOrOrthRadius_of_ne hAC]
    intro hB_mem
    have hB_eq := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hA hB_mem).mpr hB
    have hC_eq := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hA
      (right_mem_affineSpan_pair ℝ A C)).mpr hC
    rcases hB_eq, hC_eq with ⟨rfl | hB', rfl | hC'⟩
    · exact hBA rfl
    · exact hBA rfl
    · exact hAC rfl
    · exact hBC (hB'.trans hC'.symm)

/-- The intersection of lineOrOrthRadius with the sphere is exactly the endpoints. -/
lemma mem_lineOrOrthRadius_inter_sphere_iff {A B C : P}
    (hA : A ∈ s) (hC : C ∈ s) (hB : B ∈ s) :
    B ∈ s.lineOrOrthRadius A C ↔ B = A ∨ B = C := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact not_mem_lineOrOrthRadius_of_mem_sphere hA hB hC hne.1 hne.2 h
  · rintro (rfl | rfl)
    · exact left_mem_lineOrOrthRadius
    · exact right_mem_lineOrOrthRadius

end Sphere

end EuclideanGeometry

end
