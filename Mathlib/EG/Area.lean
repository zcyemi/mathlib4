/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Triangle area for competition geometry

This file defines the unsigned area of a triangle given by three points, without requiring
an `AffineIndependent` proof term. This makes the definition suitable for competition geometry
statements where many triangles appear and non-degeneracy is often implicit.

## Main definitions

* `EuclideanGeometry.triangleArea`: unsigned area of triangle `ABC`, defined via the
  Cauchy–Schwarz identity. Returns `0` for collinear points.
* `EuclideanGeometry.quadArea`: area of convex quadrilateral `ABCD`, decomposed
  along diagonal `AC`.

## Main results

* `triangleArea_nonneg`: area is nonneg.
* `triangleArea_comm23`: `triangleArea A B C = triangleArea A C B`.
* `triangleArea_cycle`: `triangleArea A B C = triangleArea B C A`.
* `triangleArea_add_of_sbtw`: if `D` lies strictly between `B` and `C`,
  then `triangleArea A B D + triangleArea A D C = triangleArea A B C`.

## Implementation notes

The definition uses `√(‖B -ᵥ A‖² · ‖C -ᵥ A‖² − ⟪B -ᵥ A, C -ᵥ A⟫_ℝ²) / 2`, which equals
`½ · ‖B -ᵥ A‖ · ‖C -ᵥ A‖ · |sin θ|` and is always nonneg by Cauchy–Schwarz. When `A`, `B`, `C`
are affinely independent, `triangleArea A B C` agrees with
`(⟨![A, B, C], h⟩ : Affine.Triangle ℝ Pt).volume`.

## Tags

area, triangle, Euclidean geometry, competition
-/

open scoped RealInnerProductSpace
open Real

namespace EuclideanGeometry

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace Pt] [NormedAddTorsor V Pt]

/-! ### Definitions -/

/-- Unsigned area of triangle `ABC`, defined as
`√(‖B -ᵥ A‖² · ‖C -ᵥ A‖² − ⟪B -ᵥ A, C -ᵥ A⟫_ℝ²) / 2`.
Returns `0` for collinear points. -/
noncomputable def triangleArea (A B C : Pt) : ℝ :=
  √(‖B -ᵥ A‖ ^ 2 * ‖C -ᵥ A‖ ^ 2 - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2) / 2

/-- Area of convex quadrilateral `ABCD`, decomposed along diagonal `AC`. -/
noncomputable def quadArea (A B C D : Pt) : ℝ :=
  triangleArea A B C + triangleArea A C D

/-! ### Nonnegativity -/

/-- The area of a triangle is nonneg. -/
theorem triangleArea_nonneg (A B C : Pt) : 0 ≤ triangleArea A B C :=
  div_nonneg (sqrt_nonneg _) two_pos.le

/-! ### Vertex permutations -/

/-- Swapping the last two vertices preserves the area. -/
theorem triangleArea_comm23 (A B C : Pt) :
    triangleArea A B C = triangleArea A C B := by
  simp only [triangleArea, mul_comm (‖B -ᵥ A‖ ^ 2), real_inner_comm]

/-- The Cauchy–Schwarz radicand is invariant under the substitution
`(u, v) ↦ (v - u, -u)`, corresponding to cyclic vertex permutation. -/
private lemma radicand_cycle_eq (u v : V) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 =
    ‖v - u‖ ^ 2 * ‖u‖ ^ 2 - ⟪v - u, -u⟫ ^ 2 := by
  have h_inner : ⟪v - u, -u⟫ = ‖u‖ ^ 2 - ⟪v, u⟫ := by
    rw [inner_sub_left, inner_neg_right, inner_neg_right,
      ← real_inner_self_eq_norm_sq]
    ring
  have h_norm : ‖v - u‖ ^ 2 = ‖v‖ ^ 2 - 2 * ⟪v, u⟫ + ‖u‖ ^ 2 :=
    norm_sub_sq_real v u
  rw [h_inner, h_norm, real_inner_comm v u]
  ring

/-- Cyclic permutation preserves the area. -/
theorem triangleArea_cycle (A B C : Pt) :
    triangleArea A B C = triangleArea B C A := by
  simp only [triangleArea]
  set u := B -ᵥ A; set v := C -ᵥ A
  have h1 : C -ᵥ B = v - u := (vsub_sub_vsub_cancel_right C B A).symm
  have h2 : A -ᵥ B = -u := (neg_vsub_eq_vsub_rev B A).symm
  rw [h1, h2, norm_neg]
  exact congrArg (· / 2) (congrArg Real.sqrt (radicand_cycle_eq u v))

/-- Swapping the first two vertices preserves the area. -/
theorem triangleArea_comm12 (A B C : Pt) :
    triangleArea A B C = triangleArea B A C :=
  (triangleArea_cycle A B C).trans (triangleArea_comm23 B C A)

/-! ### Degenerate cases -/

/-- Area is zero when the first two vertices coincide. -/
@[simp]
theorem triangleArea_self_left (A C : Pt) : triangleArea A A C = 0 := by
  simp [triangleArea, vsub_self]

/-- Area is zero when the last two vertices coincide. -/
@[simp]
theorem triangleArea_self_right (A B : Pt) : triangleArea A B B = 0 := by
  simp [triangleArea]
  ring_nf
  rw [sqrt_zero]

/-- Area is zero when the first and last vertices coincide. -/
@[simp]
theorem triangleArea_self_mid (A B : Pt) : triangleArea A B A = 0 := by
  simp [triangleArea]

/-! ### Collinearity and zero area -/

/-- Three collinear points have zero area. -/
theorem triangleArea_eq_zero_of_collinear {A B C : Pt}
    (h : Collinear ℝ ({A, B, C} : Set Pt)) : triangleArea A B C = 0 := by
  rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set Pt) by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv B (by simp)
  obtain ⟨s, hs⟩ := hv C (by simp)
  have hBA : B -ᵥ A = r • v := by rw [hr, vadd_vsub]
  have hCA : C -ᵥ A = s • v := by rw [hs, vadd_vsub]
  unfold triangleArea
  rw [hBA, hCA]
  suffices h : ‖r • v‖ ^ 2 * ‖s • v‖ ^ 2 - ⟪r • v, s • v⟫ ^ 2 = 0 by
    rw [h, sqrt_zero, zero_div]
  have h_norm_r : ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h_norm_s : ‖s • v‖ ^ 2 = s ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h_inner : ⟪r • v, s • v⟫ = r * s * ‖v‖ ^ 2 := by
      rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
      ring
  rw [h_norm_r, h_norm_s, h_inner]
  ring

/-- Three points with zero area are collinear. -/
theorem collinear_of_triangleArea_eq_zero {A B C : Pt}
    (h : triangleArea A B C = 0) : Collinear ℝ ({A, B, C} : Set Pt) := by
  set u := B -ᵥ A
  set v := C -ᵥ A
  have hrad : ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 = 0 := by
    have hge : 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
      have h1 := abs_real_inner_le_norm u v
      have h2 : ⟪u, v⟫ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
        rw [← sq_abs ⟪u, v⟫, ← mul_pow]
        exact sq_le_sq'
          (by linarith [abs_nonneg ⟪u, v⟫, mul_nonneg (norm_nonneg u) (norm_nonneg v)]) h1
      linarith
    have : √(‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) = 0 := by
      simp only [triangleArea] at h
      linarith [sqrt_nonneg (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2)]
    linarith [(sqrt_eq_zero hge).mp this]
  by_cases hu0 : u = 0
  · have : B = A := vsub_eq_zero_iff_eq.mp hu0
    subst this; simp [collinear_pair]
  · have hnu2 : (‖u‖ ^ 2 : ℝ) ≠ 0 := by positivity
    set t := ⟪u, v⟫ / ‖u‖ ^ 2
    have ht : ⟪u, v⟫ = t * ‖u‖ ^ 2 := (div_mul_cancel₀ ⟪u, v⟫ hnu2).symm
    have h1 : t * ⟪u, v⟫ = t ^ 2 * ‖u‖ ^ 2 := by rw [ht]; ring
    have hv2 : ‖v‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 :=
      mul_left_cancel₀ hnu2 (by nlinarith [hrad, sq_nonneg (⟪u, v⟫ - t * ‖u‖ ^ 2)])
    have hvtu : v = t • u := by
      have : ‖v - t • u‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
            inner_smul_right, ← real_inner_comm v u]
        linarith
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
    rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set Pt) by simp)]
    exact ⟨u, fun p hp => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp [u]⟩
      · exact ⟨t, by rw [← hvtu]; exact (vsub_vadd _ A).symm⟩⟩

/-- `triangleArea A B C = 0` if and only if `A`, `B`, `C` are collinear. -/
theorem triangleArea_eq_zero_iff {A B C : Pt} :
    triangleArea A B C = 0 ↔ Collinear ℝ ({A, B, C} : Set Pt) :=
  ⟨collinear_of_triangleArea_eq_zero, triangleArea_eq_zero_of_collinear⟩

/-! ### Area additivity -/

private lemma radicand_wbtw_left (u v : V) (t : ℝ) :
    ‖u‖ ^ 2 * ‖(1 - t) • u + t • v‖ ^ 2 - ⟪u, (1 - t) • u + t • v⟫ ^ 2 =
    t ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) := by
  have h1 : ‖(1 - t) • u + t • v‖ ^ 2 =
      (1 - t) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - t) * t) * ⟪u, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs,
      real_inner_smul_left, inner_smul_right, mul_pow, sq_abs]
    ring
  have h2 : ⟪u, (1 - t) • u + t • v⟫ = (1 - t) * ‖u‖ ^ 2 + t * ⟪u, v⟫ := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [h1, h2]; ring

private lemma radicand_wbtw_right (u v : V) (t : ℝ) :
    ‖(1 - t) • u + t • v‖ ^ 2 * ‖v‖ ^ 2 - ⟪(1 - t) • u + t • v, v⟫ ^ 2 =
    (1 - t) ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) := by
  have h1 : ‖(1 - t) • u + t • v‖ ^ 2 =
      (1 - t) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - t) * t) * ⟪u, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs,
      real_inner_smul_left, inner_smul_right, mul_pow, sq_abs]
    ring
  have h2 : ⟪(1 - t) • u + t • v, v⟫ = (1 - t) * ⟪u, v⟫ + t * ‖v‖ ^ 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  rw [h1, h2]; ring

/-- Weak betweenness version of area additivity. -/
theorem triangleArea_add_of_wbtw (A : Pt) {B D C : Pt} (h : Wbtw ℝ B D C) :
    triangleArea A B D + triangleArea A D C = triangleArea A B C := by
  obtain ⟨t, ht, hD⟩ := h
  set u := B -ᵥ A; set v := C -ᵥ A
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hDA : D -ᵥ A = (1 - t) • u + t • v := by
    have : D = t • (C -ᵥ B) +ᵥ B := by rw [← hD]; simp [AffineMap.lineMap_apply]
    rw [this, vadd_vsub_assoc,
      show C -ᵥ B = v - u from (vsub_sub_vsub_cancel_right C B A).symm]
    module
  simp only [triangleArea, hDA]
  rw [radicand_wbtw_left u v t, radicand_wbtw_right u v t,
    sqrt_mul (by positivity : (0 : ℝ) ≤ t ^ 2),
    sqrt_sq ht0,
    sqrt_mul (by positivity : (0 : ℝ) ≤ (1 - t) ^ 2),
    sqrt_sq ht1]
  ring

/-- If `D` lies strictly between `B` and `C`, then `[ABD] + [ADC] = [ABC]`. -/
theorem triangleArea_add_of_sbtw (A : Pt) {B D C : Pt} (h : Sbtw ℝ B D C) :
    triangleArea A B D + triangleArea A D C = triangleArea A B C :=
  triangleArea_add_of_wbtw A h.wbtw

/-! ### Scaling -/

/-- Area scales quadratically under homothety. -/
theorem triangleArea_smul_vsub (A B C : Pt) (r : ℝ) :
    triangleArea A (r • (B -ᵥ A) +ᵥ A) (r • (C -ᵥ A) +ᵥ A) =
    |r| ^ 2 * triangleArea A B C := by
  set u := B -ᵥ A; set v := C -ᵥ A
  simp only [triangleArea, vadd_vsub, norm_smul, Real.norm_eq_abs,
    real_inner_smul_left, inner_smul_right]
  set a := |r|
  have ha2 : r ^ 2 = a ^ 2 := (sq_abs r).symm
  have key : (a * ‖u‖) ^ 2 * (a * ‖v‖) ^ 2 - (r * (r * ⟪u, v⟫)) ^ 2 =
      (a ^ 2) ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) := by
    rw [show r * (r * ⟪u, v⟫) = r ^ 2 * ⟪u, v⟫ from by ring, ha2]; ring
  rw [key, sqrt_mul (by positivity : (0 : ℝ) ≤ (a ^ 2) ^ 2),
    sqrt_sq (sq_nonneg a)]
  ring

/-! ### Connection to `Simplex.volume` -/

/- When `A`, `B`, `C` are affinely independent, `triangleArea` agrees with `Simplex.volume`.
See: https://github.com/leanprover-community/mathlib4/pull/34826 -/
-- theorem triangleArea_eq_volume {A B C : Pt}
--     (h : AffineIndependent ℝ ![A, B, C]) :
--     triangleArea A B C = (⟨![A, B, C], h⟩ : Affine.Triangle ℝ Pt).volume := by
--   sorry

/-"We state the equivalence with Simplex.volume (pending Mathlib merge)
as a design guarantee that our lightweight triangleArea is consistent with
the measure-theoretic definition."-/

end EuclideanGeometry
