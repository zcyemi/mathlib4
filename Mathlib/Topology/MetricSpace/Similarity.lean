/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
import Mathlib.Topology.MetricSpace.Congruence

/-!
# Similarities

This file defines `Similar`, i.e., the equivalence between indexed sets of points in a metric space
where all corresponding pairwise distances have the same ratio. The motivating example is
triangles in the plane.

## Implementation notes

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation
Let `P₁` and `P₂` be metric spaces, let `ι` be an index set, and let `v₁ : ι → P₁` and
`v₂ : ι → P₂` be indexed families of points.

* `(v₁ ∼ v₂ : Prop)` represents that `(v₁ : ι → P₁)` and `(v₂ : ι → P₂)` are similar.
-/

open scoped NNReal

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]

/-- Similarity between indexed sets of vertices v₁ and v₂.
Use `open scoped Similar` to access the `v₁ ∼ v₂` notation. -/
def Similar (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similar] infixl:25 " ∼ " => Similar

/-- Similarity holds if and only if all extended distances are proportional. -/
lemma similar_iff_exists_edist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) :=
  Iff.rfl

/-- Similarity holds if and only if all extended distances between points with different
indices are proportional. -/
lemma similar_iff_exists_pairwise_edist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_edist_eq]
  refine ⟨?_, ?_⟩ <;> rintro ⟨r, hr, h⟩ <;> refine ⟨r, hr, fun i₁ i₂ ↦ ?_⟩
  · exact fun _ ↦ h i₁ i₂
  · by_cases hi : i₁ = i₂
    · simp [hi]
    · exact h hi

lemma Congruent.similar {v₁ : ι → P₁} {v₂ : ι → P₂} (h : Congruent v₁ v₂) : Similar v₁ v₂ :=
  ⟨1, one_ne_zero, fun i₁ i₂ ↦ by simpa using h i₁ i₂⟩

namespace Similar

/-- A similarity scales extended distance. Forward direction of `similar_iff_exists_edist_eq`. -/
alias ⟨exists_edist_eq, _⟩ := similar_iff_exists_edist_eq

/-- Similarity follows from scaled extended distance. Backward direction of
`similar_iff_exists_edist_eq`. -/
alias ⟨_, of_exists_edist_eq⟩ := similar_iff_exists_edist_eq

/-- A similarity pairwise scales extended distance. Forward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨exists_pairwise_edist_eq, _⟩ := similar_iff_exists_pairwise_edist_eq

/-- Similarity follows from pairwise scaled extended distance. Backward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨_, of_exists_pairwise_edist_eq⟩ := similar_iff_exists_pairwise_edist_eq

@[refl] protected lemma refl (v₁ : ι → P₁) : v₁ ∼ v₁ :=
  ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩

@[symm] protected lemma symm (h : v₁ ∼ v₂) : v₂ ∼ v₁ := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff _ ENNReal.coe_ne_top, h]
  norm_cast

lemma _root_.similar_comm : v₁ ∼ v₂ ↔ v₂ ∼ v₁ := ⟨Similar.symm, Similar.symm⟩

@[trans] protected lemma trans (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃) : v₁ ∼ v₃ := by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul, mul_assoc, h₁, h₂]

/-- Change the index set ι to an index ι' that maps to ι. -/
lemma index_map (h : v₁ ∼ v₂) (f : ι' → ι) : (v₁ ∘ f) ∼ (v₂ ∘ f) := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h

/-- Change between equivalent index sets ι and ι'. -/
@[simp]
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ∼ v₂ ∘ f ↔ v₁ ∼ v₂ := by
  refine ⟨fun h => ?_, fun h => Similar.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

variable {ι₁ ι₂ : Type*}

/-- Reindexing both families by different equivs preserves similarity when composed. -/
lemma reindex {v₁ : ι → P₁} {v₂ : ι → P₂} (e₁ : ι₁ ≃ ι) (e₂ : ι₂ ≃ ι) :
    v₁ ∘ e₁ ∼ v₂ ∘ e₂ ↔ v₁ ∼ v₂ ∘ (e₁.symm.trans e₂) := by
  rw [index_equiv e₁]
  simp only [Function.comp_def]
  constructor
  · intro h
    convert h using 1
    ext i
    simp [Equiv.trans]
  · intro h
    convert h using 1
    ext i
    simp [Equiv.trans]

end Similar

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/-- Similarity holds if and only if all non-negative distances are proportional. -/
lemma similar_iff_exists_nndist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) :=
  exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

/-- Similarity holds if and only if all non-negative distances between points with different
indices are proportional. -/
lemma similar_iff_exists_pairwise_nndist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/-- Similarity holds if and only if all distances are proportional. -/
lemma similar_iff_exists_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) :=
  similar_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

/-- Similarity holds if and only if all distances between points with different indices are
proportional. -/
lemma similar_iff_exists_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

/-- Similarity holds if and only if all distances are proportional with a positive real ratio. -/
lemma similar_iff_exists_pos_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ, 0 < r ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_dist_eq]
  constructor
  · rintro ⟨r_nn, hr_ne, hdist⟩
    refine ⟨r_nn.toReal, ?_, ?_⟩
    · positivity
    · intro i₁ i₂
      have : (r_nn : ℝ) = r_nn.toReal := by simp [NNReal.coe_toReal]
      rw [← this]
      exact_mod_cast hdist i₁ i₂
  · rintro ⟨r, hr_pos, hdist⟩
    refine ⟨Real.toNNReal r, ?_, ?_⟩
    · simp [hr_pos]
    · intro i₁ i₂
      have : r = (Real.toNNReal r).toReal := by simp [Real.toNNReal_pos.mpr hr_pos]
      rw [this]
      exact_mod_cast hdist i₁ i₂

/-- Similarity holds if and only if all distances between points with different indices are
proportional with a positive real ratio. -/
lemma similar_iff_exists_pairwise_pos_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ, 0 < r ∧ Pairwise fun i₁ i₂ ↦ (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_pairwise_dist_eq]
  constructor
  · rintro ⟨r_nn, hr_ne, hdist⟩
    refine ⟨r_nn.toReal, ?_, ?_⟩
    · positivity
    · intro i₁ i₂ hi
      have : (r_nn : ℝ) = r_nn.toReal := by simp [NNReal.coe_toReal]
      rw [← this]
      exact_mod_cast hdist hi
  · rintro ⟨r, hr_pos, hdist⟩
    refine ⟨Real.toNNReal r, ?_, ?_⟩
    · simp [hr_pos]
    · intro i₁ i₂ hi
      have : r = (Real.toNNReal r).toReal := by simp [Real.toNNReal_pos.mpr hr_pos]
      rw [this]
      exact_mod_cast hdist hi

namespace Similar

/-- A similarity scales non-negative distance. Forward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨exists_nndist_eq, _⟩ := similar_iff_exists_nndist_eq

/-- Similarity follows from scaled non-negative distance. Backward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨_, of_exists_nndist_eq⟩ := similar_iff_exists_nndist_eq

/-- A similarity scales distance. Forward direction of `similar_iff_exists_dist_eq`. -/
alias ⟨exists_dist_eq, _⟩ := similar_iff_exists_dist_eq

/-- Similarity follows from scaled distance. Backward direction of
`similar_iff_exists_dist_eq`. -/
alias ⟨_, of_exists_dist_eq⟩ := similar_iff_exists_dist_eq

/-- A similarity pairwise scales non-negative distance. Forward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨exists_pairwise_nndist_eq, _⟩ := similar_iff_exists_pairwise_nndist_eq

/-- Similarity follows from pairwise scaled non-negative distance. Backward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨_, of_exists_pairwise_nndist_eq⟩ := similar_iff_exists_pairwise_nndist_eq

/-- A similarity pairwise scales distance. Forward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨exists_pairwise_dist_eq, _⟩ := similar_iff_exists_pairwise_dist_eq

/-- Similarity follows from pairwise scaled distance. Backward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pairwise_dist_eq⟩ := similar_iff_exists_pairwise_dist_eq

/-- A similarity scales distance with positive real ratio. Forward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨exists_pos_dist_eq, _⟩ := similar_iff_exists_pos_dist_eq

/-- Similarity follows from scaled distance with positive real ratio. Backward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨_, of_exists_pos_dist_eq⟩ := similar_iff_exists_pos_dist_eq

/-- A similarity pairwise scales distance with positive real ratio. Forward direction of
`similar_iff_exists_pairwise_pos_dist_eq`. -/
alias ⟨exists_pairwise_pos_dist_eq, _⟩ := similar_iff_exists_pairwise_pos_dist_eq

/-- Similarity follows from pairwise scaled distance with positive real ratio. Backward direction
of `similar_iff_exists_pairwise_pos_dist_eq`. -/
alias ⟨_, of_exists_pairwise_pos_dist_eq⟩ := similar_iff_exists_pairwise_pos_dist_eq

end Similar

/-- For two similar families, there exists a positive ratio such that the distances between
corresponding points are proportional. -/
theorem exist_dist_eq_mul_dist_of_similar {v₁ : ι → P₁} {v₂ : ι → P₂} (h : v₁ ∼ v₂)
    (i₁ i₂ : ι) :
    ∃ r : ℝ, 0 < r ∧ dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂) := by
  rw [similar_iff_exists_pos_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  use r
  exact ⟨hr_pos, hdist i₁ i₂⟩

variable {a b c : P₁} {a' b' c' : P₂}

/-- If all the corresponding sides of two triangles are proportional with a positive real ratio,
then the triangles are similar. -/
theorem similar_of_three_pos_dist_eq (h : ∃ r : ℝ, 0 < r ∧ dist a b = r * dist a' b' ∧
    dist b c = r * dist b' c' ∧ dist c a = r * dist c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  rcases h with ⟨r, hr_pos, hd₁, hd₂, hd₃⟩
  set r_nn : ℝ≥0 := Real.toNNReal r with hr_nn
  rw [similar_iff_exists_dist_eq]
  use r_nn
  have h_ne : r_nn ≠ 0 := by
    rw [hr_nn]
    simp
    linarith
  have hr : r = r_nn.toReal := by
    rw [hr_nn]
    simp
    positivity
  rw [hr] at hd₁ hd₂ hd₃
  refine ⟨h_ne, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

namespace Similar

variable {t₁ : Fin 3 → P₁} {t₂ : Fin 3 → P₂}

/-- Reindexing both triangles by the same permutation preserves similarity. -/
theorem reindex_perm (h : t₁ ∼ t₂) (e : Equiv.Perm (Fin 3)) :
    (t₁ ∘ e) ∼ (t₂ ∘ e) := Similar.index_map h e

theorem comm_left (h : ![a, b, c] ∼ ![a', b', c']) :
    ![b, a, c] ∼ ![b', a', c'] := by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp; rfl
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp; rfl
  grind [reindex_perm]

theorem comm_right (h : ![a, b, c] ∼ ![a', b', c']) :
    ![a, c, b] ∼ ![a', c', b'] := by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp; rfl
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp; rfl
  grind [reindex_perm]

theorem reverse (h : ![a, b, c] ∼ ![a', b', c']) :
    ![c, b, a] ∼ ![c', b', a'] := by
  have hl : ![c, b, a] = ![a, b, c] ∘ Equiv.swap 0 2 := by
    ext i
    fin_cases i <;> simp; rfl
  have hr : ![c', b', a'] = ![a', b', c'] ∘ Equiv.swap 0 2 := by
    ext i
    fin_cases i <;> simp; rfl
  grind [reindex_perm]

end Similar

end PseudoMetricSpace
