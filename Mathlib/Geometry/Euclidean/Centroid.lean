import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Centroid of a Triangle

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

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]


variable {n : ℕ}

namespace Simplex


abbrev centroid {n : ℕ} (t : Affine.Simplex ℝ P n) : P :=
  Finset.univ.centroid ℝ t.points

theorem centroid_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.centroid ∈ affineSpan ℝ (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one ℝ _ (card_fin (n + 1))

variable [NeZero n]


def faceOppositeCentroid (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).centroid


theorem faceOppositeCentroid_eq (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((affineCombination ℝ {i}ᶜ s.points) fun _ ↦ (↑n)⁻¹) := by
  unfold faceOppositeCentroid

  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by
    rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid]
  rw [centroid_def]
  rw [centroidWeights_eq_const]
  rw [card_compl]
  simp
  rfl




theorem faceOppositeCentroid_vsub_faceOppositeCentroid (s : Affine.Simplex ℝ P n)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    s.faceOppositeCentroid i -ᵥ s.faceOppositeCentroid j =
    ((1:ℝ) / n) • (s.points j -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq, faceOppositeCentroid_eq]

  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
      (by simp [sum_const,card_compl]) (s.points i)]
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
      (by simp [sum_const,card_compl]) (s.points i)]
  sorry



theorem faceOppositeCentroid_mem_affineSpan (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan ℝ (Set.range s.points) := by
  unfold faceOppositeCentroid
  have h : Set.range (s.faceOpposite i).points ⊆ Set.range s.points := by
    intro j hj
    rcases hj with ⟨k, _, rfl⟩
    apply Set.mem_range_self
  apply affineSpan_mono _ h
  exact centroid_mem_affineSpan (s.faceOpposite i)


def median (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  line[ℝ, s.points i, s.faceOppositeCentroid i]


theorem faceOppositeCentroid_mem_median (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [median, right_mem_affineSpan_pair]

theorem point_mem_median (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [median, left_mem_affineSpan_pair]

theorem points_vsub_faceOppositeCentroid_eq_n_add_one_times_centroid_vsub_faceOppositeCentroid (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i = ((n + 1):ℝ) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  rw [Simplex.centroid, Finset.centroid_def]
  sorry

theorem centroid_mem_segment_faceOppositeCentroid_points (s : Simplex ℝ P n) (i : Fin (n + 1)) :
   s.centroid ∈ affineSegment ℝ (s.faceOppositeCentroid i) (s.points i) := by
  unfold affineSegment
  simp
  use ((1/(n + 1)):ℝ)
  constructor
  · constructor
    · refine one_div_nonneg.mpr ?_
      norm_cast
      omega
    · refine div_le_self ?_ ?_
      simp
      norm_cast
      omega
  · rw [AffineMap.lineMap_apply]
    rw [points_vsub_faceOppositeCentroid_eq_n_add_one_times_centroid_vsub_faceOppositeCentroid]
    rw [← smul_assoc, show (1 / ((n:ℝ) + 1)) • ((n:ℝ) + 1) = 1 by rw[smul_eq_mul, div_mul_eq_mul_div, one_mul, div_self];ring_nf;norm_cast;omega]
    simp only [one_smul, vsub_vadd]

theorem wbtw_points_centroid_faceOppositeCentroid (s : Simplex ℝ P n) (i : Fin (n + 1)):
    Wbtw ℝ (s.faceOppositeCentroid i) s.centroid (s.points i) := centroid_mem_segment_faceOppositeCentroid_points s i


theorem centroid_mem_median (s : Simplex ℝ P n) (i : Fin (n + 1)) :
  s.centroid ∈ s.median i := by
  rw [median]
  have h := centroid_mem_segment_faceOppositeCentroid_points s i
  refine Wbtw.mem_affineSpan ?_
  exact Wbtw.symm h

theorem medians_concurrent (s : Simplex ℝ P n) :
    ∀ i : Fin (n + 1), s.centroid ∈ s.median i := by
  simp [centroid_mem_median]


theorem eq_centroid_of_forall_mem_median {s : Simplex ℝ P n} {p : P}
    (h : ∀ i, p ∈ s.median i) : p = s.centroid := by
  -- intersect medians at i = 0 and i = 1 to pin down the centroid
  have h0 := h 0
  have h1 := h 1
  by_cases h01 : (0 : Fin (n + 1)) = 1
  · absurd h01
    simp
  · have hc := medians_concurrent s
    have hc0 := hc 0
    have hc1 := hc 1
    by_contra hne

    sorry

theorem dist_vertex_centroid_eq_n_mul_centroid_face_dist (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    dist (s.points i) s.centroid = n * dist s.centroid (s.faceOppositeCentroid i) := by
  have h1 : (n + 1) * dist s.centroid (s.faceOppositeCentroid i) = dist (s.points i) (s.faceOppositeCentroid i) := by
    rw[dist_eq_norm_vsub, dist_eq_norm_vsub, show ((n:ℝ) + 1) = ((↑(n + 1)):ℝ) by norm_cast , ←Int.norm_natCast]
    calc
    _ = ‖((↑(n + 1)):ℝ) • (s.centroid -ᵥ s.faceOppositeCentroid i)‖ := by
      rw[norm_smul]
      congr
    _ = ‖s.points i -ᵥ s.faceOppositeCentroid i‖ := by
      congr 1
      rw[points_vsub_faceOppositeCentroid_eq_n_add_one_times_centroid_vsub_faceOppositeCentroid]
      norm_cast
  have h2 : dist (s.points i) (s.faceOppositeCentroid i) = dist s.centroid (s.faceOppositeCentroid i) + dist (s.points i) s.centroid := by
    have h:= wbtw_points_centroid_faceOppositeCentroid s i
    nth_rw 2 [dist_comm]
    nth_rw 3 [dist_comm]
    rw[Wbtw.dist_add_dist]
    nth_rw 1 [dist_comm]
    exact h
  rw [← h1, add_mul, one_mul, add_comm] at h2
  simp at h2
  exact id (Eq.symm h2)



end Simplex


namespace Triangle

open Affine Simplex


/-- The centroid lies in the affine span of the triangle's vertices. -/
theorem centroid_mem_affineSpan (t : Triangle ℝ P) :
    t.centroid ∈ affineSpan ℝ (Set.range t.points) := by
  unfold Affine.Simplex.centroid
  unfold Finset.centroid
  simp [affineCombination_mem_affineSpan]








-- /-- The vector from a vertex to the centroid equals one third of the sum of
--     vectors from that vertex to the other two vertices. -/
-- theorem vsub_centroid (t : Triangle ℝ P) (i : Fin 3) :
--   t.points i -ᵥ t.centroid = (1/3 : ℝ) • ((t.points i -ᵥ t.points ((i + 1) % 3)) +
--                                         (t.points i -ᵥ t.points ((i + 2) % 3))) :=
--   sorry

-- /-- The centroid is the intersection point of the three medians, and each median
--     is divided by the centroid in a 2:1 ratio (from vertex to opposite side). -/
-- theorem centroid_eq_medians_intersection (t : Triangle ℝ P) :
--   ∃ (t₀ t₁ t₂ : ℝ),
--     t.centroid = t₀ • (midpoint ℝ (t.points 1) (t.points 2) -ᵥ t.points 0) +ᵥ t.points 0 ∧
--     t.centroid = t₁ • (midpoint ℝ (t.points 0) (t.points 2) -ᵥ t.points 1) +ᵥ t.points 1 ∧
--     t.centroid = t₂ • (midpoint ℝ (t.points 0) (t.points 1) -ᵥ t.points 2) +ᵥ t.points 2 :=
--   ⟨2/3, 2/3, 2/3, sorry, sorry, sorry⟩

-- /-- The centroid divides each median in a 2:1 ratio (from vertex to opposite side's midpoint). -/
-- theorem centroid_divides_median (t : Triangle ℝ P) (i : Fin 3) :
--   t.centroid = (2/3 : ℝ) • (midpoint ℝ (t.points ((i + 1) % 3)) (t.points ((i + 2) % 3)) -ᵥ t.points i) +ᵥ t.points i :=by
--   sorry

-- /-- The centroid can also be expressed as the arithmetic mean of the three vertices. -/
-- theorem centroid_eq_average (t : Triangle ℝ P) :
--   t.centroid = Finset.univ.affineCombination ℝ t.points (Function.const (Fin 3) (1/3 : ℝ)) := by
--   unfold Affine.Simplex.centroid
--   unfold centroid
--   unfold centroidWeights
--   simp



end Triangle

end Affine
