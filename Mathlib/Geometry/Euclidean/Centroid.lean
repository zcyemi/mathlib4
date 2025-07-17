import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Centroid of a Simplex

This file defines the centroid of a triangle as the average of its vertices,
and proves basic properties about it, such as:
- It lies in the affine span of the triangle's vertices
- It can be expressed as a weighted sum of vectors from vertices
- It is the intersection point of the three medians
- It divides each median in a 2:1 ratio

## Tags

triangle, centroid, barycenter, geometric center
-/

noncomputable section

namespace Affine

open Finset AffineSubspace EuclideanGeometry

variable {k : Type*} {V : Type*} {P : Type*}
variable [DivisionRing k] [CharZero k] [AddCommGroup V]
variable [Module k V]
variable [AffineSpace V P]

variable {n : ℕ}

namespace Simplex


/-- Centroid is an affineCombination of the points in simplex with centroid weight. -/
abbrev centroid (t : Affine.Simplex k P n) : P := Finset.univ.centroid k t.points

theorem centroid_mem_affineSpan {n : ℕ} (s : Simplex k P n) :
    s.centroid ∈ affineSpan k (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

theorem centroid_vsub_point {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = ((1:k) / (n + 1)) • ∑ x, (s.points x -ᵥ s.points i) := by
  rw [centroid, Finset.centroid_def]
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, centroidWeights_apply, card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, vadd_vsub, one_div,←smul_sum]
  · field_simp; exact div_self (by norm_cast)

variable [NeZero n]

/-- A faceOppositeCentroid is the centroid of simplex faceOpposite for the i indexed point. -/
def faceOppositeCentroid (s : Affine.Simplex k P n) (i : Fin (n + 1)) : P :=
    (s.faceOpposite i).centroid

theorem faceOppositeCentroid_mem_affineSpan (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan k (Set.range s.points) := by
  unfold faceOppositeCentroid
  have h : Set.range (s.faceOpposite i).points ⊆ Set.range s.points := by
    intro j hj
    rcases hj with ⟨k, _, rfl⟩
    apply Set.mem_range_self
  apply affineSpan_mono _ h
  exact centroid_mem_affineSpan (s.faceOpposite i)


theorem faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((affineCombination k {i}ᶜ s.points) fun _ ↦ (↑n)⁻¹) := by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid, centroid_def, centroidWeights_eq_const, card_compl]
  simp only [Fintype.card_fin, card_singleton, add_tsub_cancel_right]
  rfl

theorem faceOppositeCentroid_vsub_point (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ (s.points i) = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_affineCombination]
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
    ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i: Fin (n+1)) : ∑ i_1 ∈ {i}ᶜ, (n:k)⁻¹ • (s.points i_1 -ᵥ s.points i) =
      ∑ i_1 : (Fin (n + 1)) , ((n:k)⁻¹ • (s.points i_1 -ᵥ s.points i)) :=by
      rw [←Finset.sum_compl_add_sum {i}]
      simp
    rw [h i]
    field_simp
    rw [smul_sum]
  simp [sum_const,card_compl]
  field_simp
  rw [div_self]
  exact NeZero.ne (n:k)

theorem faceOppositeCentroid_eq_sum_vsub_vadd (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n:k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ (s.points i) := by
  rw [←faceOppositeCentroid_vsub_point s i]
  rw [vsub_vadd]

theorem smul_faceOppositeCentroid_vsub_point (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    (n:k) • (s.faceOppositeCentroid i -ᵥ s.points i) =  ∑ x, (s.points x -ᵥ s.points i) :=by
  field_simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, div_self (NeZero.ne ( n : k)),
    one_smul]


theorem vadd_vsub_vadd_eq (v1 v2 : V) (p1 p2 : P) : (v1 +ᵥ p1) -ᵥ (v2 +ᵥ p2) = (v1 -ᵥ v2) +ᵥ (p1 -ᵥ p2) := by
  rw [vsub_vadd_eq_vsub_sub]
  field_simp
  rw [sub_add_comm,add_comm, ←add_sub_assoc, vadd_vsub_assoc]

theorem faceOppositeCentroid_vsub_faceOppositeCentroid (s : Affine.Simplex k P n)
    (i j : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.faceOppositeCentroid j =
    (n : k)⁻¹ • (s.points j -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s i]
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s j]
  rw [vadd_vsub_vadd_eq _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n+1)): ∑ x,  (s.points x -ᵥ s.points i) = ∑ x,  (s.points x -ᵥ s.points 0
      - (s.points i-ᵥ s.points 0)) :=by
   apply sum_congr rfl
   simp
  simp_rw [h1 i, h1 j, sum_sub_distrib]
  field_simp
  rw [smul_sub,smul_sub]
  simp only [one_div, sub_sub_sub_cancel_left]
  rw [←smul_sub,←smul_sub]
  rw [vsub_sub_vsub_cancel_right]
  have : (s.points i -ᵥ s.points j) = -(s.points j -ᵥ s.points i) := by simp
  rw [this]
  rw [←sub_eq_add_neg]
  field_simp
  rw [add_smul, sub_eq_iff_eq_add ,one_smul, smul_add, add_comm]
  field_simp
  have : ((1:k) / ↑n) • n • (s.points j -ᵥ s.points i) = (n : k)⁻¹ •
      (n : k) • (s.points j -ᵥ s.points i) := by
    norm_cast0
    congr 1
    rw [one_div]
  rw [this,smul_smul,inv_eq_one_div,one_div_mul_cancel (NeZero.ne (n:k)), one_smul]

theorem faceOppositeCentroid_vsub_centroid (s : Simplex k P n) (i : Fin (n + 1)) :
    ((n + 1) : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) =
    s.faceOppositeCentroid i -ᵥ s.points i := by
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i), faceOppositeCentroid_vsub_point,
    centroid_vsub_point, ← sub_smul, smul_smul]
  congr
  field_simp [mul_sub]
  rw [add_div, one_div, div_self (NeZero.ne (n : k)), div_self (by norm_cast)]
  norm_num

/-- Commandino's theorem -/
theorem smul_centroid_vsub_faceOppositeCentroid_eq_point_vsub_centroid_eq (s : Simplex k P n)
    (i : Fin (n + 1)) :
    (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) = s.points i -ᵥ s.centroid := by
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i), faceOppositeCentroid_vsub_point,
    centroid_vsub_point, ← neg_vsub_eq_vsub_rev, centroid_vsub_point, ← sub_smul, smul_smul,
    ← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  field_simp [sub_eq_iff_eq_add, NeZero.ne (n : k)]
  rw [div_self (by norm_cast)]


/-- The centroid, a vertex, and the corresponding faceOppositeCentroid of a simplex are collinear.
-/
theorem collinear_point_centroid_faceOppositeCentroid (s : Simplex k P n) (i : Fin (n + 1)) :
    Collinear k {s.points i, s.centroid, s.faceOppositeCentroid i} := by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
    rw [← neg_vsub_eq_vsub_rev, neg_smul_neg,
      smul_centroid_vsub_faceOppositeCentroid_eq_point_vsub_centroid_eq, vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _


section median

omit [CharZero k]

/-- Define median as an line throught the point of simplex and corosponed faceOppositeCentroid. -/
def median (s : Simplex k P n) (i : Fin (n + 1)) : AffineSubspace k P :=
  line[k, s.points i, s.faceOppositeCentroid i]

theorem faceOppositeCentroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [median, right_mem_affineSpan_pair]

theorem point_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [median, left_mem_affineSpan_pair]

theorem centroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
  s.centroid ∈ s.median i := by
  rw [median]
  sorry

theorem eq_centroid_of_forall_mem_median {s : Simplex k P n} {p : P} (h : ∀ i, p ∈ s.median i) :
    p = s.centroid := by
  rw [← @vsub_eq_zero_iff_eq V]
  sorry


end median


end Simplex

end Affine
