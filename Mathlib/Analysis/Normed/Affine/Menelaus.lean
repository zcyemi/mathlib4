/-
Copyright (c) 2026 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Menelaus
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Between

/-!
# Menelaus' theorem.

This file proves Menelaus' theorem in a `NormedAddTorsor`.

## References

* https://en.wikipedia.org/wiki/Menelaus%27_theorem

-/

public section

open scoped Affine

variable {𝕜 V P : Type*} [SeminormedAddCommGroup V] [NormedField 𝕜] [NormedSpace 𝕜 V]

namespace Affine.Triangle


section OrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [MetricSpace P] [NormedAddTorsor V P] [Module 𝕜 V]


theorem div_one_sub_nonneg_iff_wbtw
    {𝕜 V P : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {a b : P} {r : 𝕜}
    (hab : a ≠ b) :
    0 ≤ r / (1 - r) ↔ Wbtw 𝕜 a (AffineMap.lineMap a b r) b := by
  rw [wbtw_lineMap_iff, or_iff_right hab, Set.mem_Icc]
  constructor
  · intro h
    rw [div_nonneg_iff] at h
    rcases h with h | h
    · exact ⟨h.1, by linarith⟩
    · exfalso
      linarith
  · rintro ⟨hr0, hr1⟩
    exact div_nonneg hr0 (sub_nonneg.mpr hr1)

theorem div_one_sub_neg_iff_not_wbtw
    {𝕜 V P : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {a b : P} {r : 𝕜}
    (hab : a ≠ b) :
    r / (1 - r) < 0 ↔ ¬ Wbtw 𝕜 a (AffineMap.lineMap a b r) b := by
  rw [← iff_not_comm, not_lt]
  symm
  exact div_one_sub_nonneg_iff_wbtw hab


variable {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P]

theorem test1 {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hprod : ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1) :
    ∃ r : Fin 3 → ℝ, (∀ i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i) = p i) ∧
      ∏ i, ‖r i‖ / ‖1 - r i‖ = 1 := by
  classical
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  refine ⟨r, hr, ?_⟩
  have hd (i : Fin 3) : dist (t.points (i + 1)) (t.points (i + 2)) ≠ 0 := by
    intro hz
    have hidx : (i + 1 : Fin 3) ≠ (i + 2 : Fin 3) := by
      fin_cases i <;> simp
    exact hidx (t.independent.injective (dist_eq_zero.mp hz))
  have hratio (i : Fin 3) : dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) =
      ‖r i‖ / ‖1 - r i‖ := by
    rw [← hr i]
    rw [dist_left_lineMap, dist_lineMap_right]
    field_simp [hd i]
  simpa [hratio] using hprod

open scoped Affine BigOperators
open Affine
open SignType
theorem prod_neg_of_odd_neg_card {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    (hne : ∀ i, q i ≠ 0)
    (hodd : Odd (Finset.univ.filter (fun i => q i < 0)).card) :
    ∏ i, q i < 0 := by
  classical
  have hsign : sign (∏ i, q i) = (-1 : SignType) ^ (Finset.univ.filter (fun i => q i < 0)).card := by
    calc
      sign (∏ i, q i) = ∏ i, sign (q i) := by
        exact map_prod signHom q Finset.univ
      _ = ∏ i, (if q i < 0 then (-1 : SignType) else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hneg : q i < 0
        · simp [sign_neg hneg, hneg]
        · have hpos : 0 < q i := lt_of_le_of_ne (le_of_not_gt hneg) (hne i).symm
          simp [sign_pos hpos, hneg]
      _ = (-1 : SignType) ^ (Finset.univ.filter (fun i => q i < 0)).card := by
        rw [Finset.prod_ite]
        simp [Finset.prod_const]
  have hsign' : sign (∏ i, q i) = (-1 : SignType) := by
    rw [hsign, SignType.pow_odd (-1 : SignType) hodd]
  exact sign_eq_neg_one_iff.mp hsign'

end OrderedField

variable [PseudoMetricSpace P] [NormedAddTorsor V P] in
/-- **Menelaus' theorem** for a triangle, expressed in terms of multiplying distances. -/
theorem prod_dist_eq_prod_dist_of_mem_line_of_collinear {t : Triangle 𝕜 P} {p : Fin 3 → P}
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hcol : Collinear 𝕜 {p 0, p 1, p 2}) :
    ∏ i, dist (t.points (i + 1)) (p i) = ∏ i, dist (p i) (t.points (i + 2)) := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  have h := (t.prod_eq_neg_prod_one_sub_iff_collinear_of_lineMap hr).mpr hcol
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_mul_distrib, ← norm_prod]
  rw [h, norm_neg]

variable [MetricSpace P] [NormedAddTorsor V P] in
/-- **Menelaus' theorem** for a triangle, expressed using division of distances. -/
theorem prod_dist_div_dist_eq_one_of_mem_line_of_collinear {t : Triangle 𝕜 P} {p : Fin 3 → P}
    (hp0 : ∀ i, p i ≠ t.points (i + 2))
    (hp : ∀ i : Fin 3, p i ∈ line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hcol : Collinear 𝕜 {p 0, p 1, p 2}) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
  have h := prod_dist_eq_prod_dist_of_mem_line_of_collinear hp hcol
  rw [Finset.prod_div_distrib, h, div_self]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ by grind [dist_ne_zero]


variable [MetricSpace P] [NormedAddTorsor V P] [Module ℝ V] in
theorem collinear_of_prod_dist_div_eq_one_of_odd_card {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hodd : Odd ({i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))}.ncard))
    (hprod : ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1) :
    Collinear ℝ {p 0, p 1, p 2} := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  sorry



variable {V P : Type*}
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P]
theorem collinear_of_prod_dist_div_eq_one_of_odd_card'
    {t : Triangle ℝ P} {p : Fin 3 → P}
    (hp : ∀ i, p i ∈ line[ℝ, t.points (i + 1), t.points (i + 2)])
    (hodd : Odd ({i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))}.ncard))
    (hprod : ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1) :
    Collinear ℝ {p 0, p 1, p 2} := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  -- 三角形的两个不同顶点不相等
  have hside_ne (i : Fin 3) : t.points (i + 1) ≠ t.points (i + 2) := by
    intro h
    have hidx : (i + 1 : Fin 3) ≠ (i + 2 : Fin 3) := by fin_cases i <;> simp
    exact hidx (t.independent.injective h)
  let q : Fin 3 → ℝ := fun i => r i / (1 - r i)
  have hratio (i : Fin 3) :
    dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = ‖q i‖ := by
    rw [← hr i,dist_left_lineMap, dist_lineMap_right, norm_div]
    field_simp [dist_ne_zero.mpr (hside_ne i)]

  -- 所以 ∏ ‖qᵢ‖ = 1
  have hnormprod : ∏ i, ‖q i‖ = 1 := by grind
  have hq_ne (i : Fin 3) : q i ≠ 0 := by
    have hprod_ne : (∏ i, ‖q i‖) ≠ 0 := by
      rw [hnormprod]
      norm_num
    have hnorm_ne : ‖q i‖ ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod_ne) i (Finset.mem_univ i)
    intro hqi
    apply hnorm_ne
    simp [hqi]

  -- Step 5:
  -- q i < 0 ↔ p i 不位于两个顶点之间
  have hneg_iff (i : Fin 3) : q i < 0 ↔ ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2)) := by
    grind [div_one_sub_neg_iff_not_wbtw]

  -- 因此 hodd 正好说明负的 q i 数量为奇数
  have hset : {i : Fin 3 | ¬ Wbtw ℝ (t.points (i + 1)) (p i) (t.points (i + 2))} =
      {i : Fin 3 | q i < 0} := by
    grind

  have hodd_q : Odd ({i : Fin 3 | q i < 0}.ncard) := by
    rw [← hset]
    exact hodd

  have hodd_filter :
      Odd (Finset.univ.filter (fun i => q i < 0)).card := by
    rw [Set.ncard_eq_toFinset_card'] at hodd_q
    simpa using hodd_q

  -- Step 6:
  -- 奇数个负因子 ⇒ ∏ qᵢ < 0
  have hqprod_neg : ∏ i, q i < 0 := by
    exact prod_neg_of_odd_neg_card hq_ne hodd_filter

  -- 同时距离条件告诉我们 |∏ qᵢ| = 1
  have hqprod_norm : ‖∏ i, q i‖ = 1 := by
    rw [norm_prod]
    exact hnormprod

  -- 负数且绝对值为 1，因此乘积就是 -1
  have hqprod_eq_neg_one : ∏ i, q i = -1 := by
    rw [Real.norm_eq_abs, abs_of_neg hqprod_neg] at hqprod_norm

    linarith





  -- Step 7:
  -- 为了把
  --
  --   ∏ (rᵢ / (1-rᵢ)) = -1
  --
  -- 化成
  --
  --   ∏ rᵢ = - ∏ (1-rᵢ)
  --
  -- 需要知道所有 1-rᵢ ≠ 0。

  have hone_sub_ne (i : Fin 3) : 1 - r i ≠ 0 := by
    intro hi
    apply hq_ne i
    simp [q, hi]

  have hden_ne : ∏ i, (1 - r i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hone_sub_ne i

  -- 得到标准有符号 Menelaus 恒等式
  have hmenelaus :
      ∏ i, r i = - ∏ i, (1 - r i) := by
    have h := hqprod_eq_neg_one
    simp only [q, Finset.prod_div_distrib] at h
    rw [div_eq_iff hden_ne] at h
    simpa using h

  -- Step 8:
  -- 使用你 LinearAlgebra.AffineSpace.Menelaus 里的逆定理
  exact
    (t.prod_eq_neg_prod_one_sub_iff_collinear_of_lineMap hr).mp
      hmenelaus




end Affine.Triangle
