import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.Convex

noncomputable section

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {k : Type*} {V : Type*} {P : Type*}
variable [DivisionRing k] [AddCommGroup V]
variable [Module k V]
variable [AffineSpace V P]
variable {n : ℕ}

/-- Centroid is an affineCombination of the points in simplex with centroid weight. -/
abbrev centroid (t : Affine.Simplex k P n) : P := Finset.univ.centroid k t.points

theorem centroid_mem_affineSpan_range [CharZero k] {n : ℕ} (s : Simplex k P n) :
    s.centroid ∈ affineSpan k (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))


theorem centroid_vsub_eq {n : ℕ} [CharZero k] (s : Simplex k P n) (p : P) :
    s.centroid -ᵥ p = ((1:k) / (n + 1)) • ∑ x, (s.points x -ᵥ p) := by
  rw [centroid, Finset.centroid_def]
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ p]
  · simp only [weightedVSubOfPoint_apply, centroidWeights_apply, card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, vadd_vsub, one_div,←smul_sum]
  · field_simp; exact div_self (by norm_cast)

theorem centroid_vsub_point_eq_smul_sum_vsub {n : ℕ} [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = ((1:k) / (n + 1)) • ∑ x, (s.points x -ᵥ s.points i) := by
  exact centroid_vsub_eq s (s.points i)

theorem centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = ((1:k) / (n + 1)) • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.points i := by
  rw [← centroid_vsub_point_eq_smul_sum_vsub s i, vsub_vadd]

theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    ((n:k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [centroid_eq_smul_sum_vsub_vadd s i]
  rw [vadd_vsub]
  rw [smul_smul]
  field_simp
  rw [div_self (by norm_cast), one_smul]

theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self, one_div] at h
  symm at h
  rw [smul_eq_zero_iff_right (by exact inv_ne_zero (by norm_cast))] at h
  exact h

theorem centroid_iff_sum_vsub_eq_zero [CharZero k] (s : Simplex k P n) (p : P) :
    p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0 := by
  constructor
  · intro h
    rw [h, centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ s.centroid]
    rw [this, sum_sub_distrib, centroid_weighted_vsub_eq_zero] at h
    simp only [sum_const, card_univ, Fintype.card_fin, zero_sub, neg_eq_zero] at h
    have h' : ((n:k) + 1) • (p -ᵥ s.centroid) = 0 := by norm_cast
    rw [smul_eq_zero_iff_right (by norm_cast)] at h'
    exact h'

variable [NeZero n]

/-- A faceOppositeCentroid is the centroid of simplex faceOpposite for the i indexed point. -/
def faceOppositeCentroid (s : Affine.Simplex k P n) (i : Fin (n + 1)) : P :=
    (s.faceOpposite i).centroid

theorem faceOppositeCentroid_mem_affineSpan [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan k (Set.range s.points) := by
  unfold faceOppositeCentroid
  have h : Set.range (s.faceOpposite i).points ⊆ Set.range s.points := by
    intro j hj
    rcases hj with ⟨k, _, rfl⟩
    apply Set.mem_range_self
  apply affineSpan_mono _ h
  exact centroid_mem_affineSpan_range (s.faceOpposite i)

theorem faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((affineCombination k {i}ᶜ s.points) fun _ ↦ (↑n)⁻¹) := by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid, centroid_def, centroidWeights_eq_const, card_compl]
  simp only [Fintype.card_fin, card_singleton, add_tsub_cancel_right]
  rfl

theorem faceOppositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
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

theorem faceOppositeCentroid_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n:k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ (s.points i) := by
  rw [←faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i]
  rw [vsub_vadd]

theorem point_vsub_faceOppositeCentroid_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points i -ᵥ s.points x) := by
  rw [← neg_vsub_eq_vsub_rev, faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, ← neg_smul,
    Lean.Grind.Ring.neg_eq_mul_neg_one, ← smul_smul, smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]

theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    (n:k) • (s.faceOppositeCentroid i -ᵥ s.points i) =  ∑ x, (s.points x -ᵥ s.points i) :=by
  field_simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, div_self (NeZero.ne ( n : k)),
    one_smul]

theorem smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    ((n + 1) : k) • (s.centroid -ᵥ s.points i) =
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) := by
  rw [smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i]
  rw [smul_centroid_vsub_point_eq_sum_vsub s i]

theorem vadd_vsub_vadd_eq (v1 v2 : V) (p1 p2 : P) : (v1 +ᵥ p1) -ᵥ (v2 +ᵥ p2) = (v1 -ᵥ v2)
    +ᵥ (p1 -ᵥ p2) := by
  rw [vsub_vadd_eq_vsub_sub]
  field_simp
  rw [sub_add_comm,add_comm, ←add_sub_assoc, vadd_vsub_assoc]

theorem faceOppositeCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Simplex k P n)
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
  rw [← smul_sub, ← smul_sub]
  rw [vsub_sub_vsub_cancel_right]
  have : (s.points i -ᵥ s.points j) = -(s.points j -ᵥ s.points i) := by simp
  rw [this, ← sub_eq_add_neg]
  field_simp
  rw [add_smul, sub_eq_iff_eq_add ,one_smul, smul_add, add_comm]
  field_simp
  have : ((1:k) / ↑n) • n • (s.points j -ᵥ s.points i) = (n : k)⁻¹ •
      (n : k) • (s.points j -ᵥ s.points i) := by
    norm_cast0
    congr 1
    rw [one_div]
  rw [this, smul_smul, inv_eq_one_div, one_div_mul_cancel (NeZero.ne (n:k)), one_smul]

theorem faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.points i =
    ((n + 1) : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i)]
  rw [faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, centroid_vsub_point_eq_smul_sum_vsub,
    ← sub_smul, smul_smul]
  congr
  field_simp [mul_sub]
  rw [add_div, one_div, div_self (NeZero.ne (n : k)), div_self (by norm_cast)]
  norm_num

theorem point_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i =
    ((n + 1) : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  rw [← neg_vsub_eq_vsub_rev, faceOppositeCentroid_vsub_point_eq_smul_vsub, ← neg_smul,
    ← neg_smul_neg, neg_vsub_eq_vsub_rev, neg_neg]

/-- Commandino's theorem -/
theorem point_vsub_centroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i)  := by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i),
    faceOppositeCentroid_vsub_point_eq_smul_sum_vsub,
    centroid_vsub_point_eq_smul_sum_vsub, ← neg_vsub_eq_vsub_rev,
    centroid_vsub_point_eq_smul_sum_vsub, ← sub_smul, smul_smul, ← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  field_simp [sub_eq_iff_eq_add, NeZero.ne (n : k)]
  rw [div_self (by norm_cast)]

theorem centroid_vsub_point_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← neg_vsub_eq_vsub_rev, point_vsub_centroid_eq_smul_vsub, ← neg_smul_neg,
    neg_vsub_eq_vsub_rev, ← neg_smul, neg_neg]

theorem centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.points i := by
  rw [← centroid_vsub_point_eq_smul_vsub, vsub_vadd]

theorem point_eq_smul_vsub_vadd_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
  rw [← neg_vsub_eq_vsub_rev, neg_smul_neg, ← point_vsub_centroid_eq_smul_vsub, vsub_vadd]

/-- The centroid, a vertex, and the corresponding faceOppositeCentroid of a simplex are collinear.
-/
theorem collinear_point_centroid_faceOppositeCentroid [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    Collinear k {s.points i, s.centroid, s.faceOppositeCentroid i} := by
  apply collinear_insert_of_mem_affineSpan_pair
  rw [point_eq_smul_vsub_vadd_centroid]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

/-- Define median as an line throught the point of simplex and corosponed faceOppositeCentroid. -/
def median (s : Simplex k P n) (i : Fin (n + 1)) : AffineSubspace k P :=
  line[k, s.points i, s.faceOppositeCentroid i]

theorem faceOppositeCentroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [median, right_mem_affineSpan_pair]

theorem point_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [median, left_mem_affineSpan_pair]

theorem centroid_mem_median [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
  s.centroid ∈ s.median i := by
  rw [median]
  have h : s.centroid = ((n:k) * (1/ (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq, centroid_vsub_point_eq_smul_vsub,
      faceOppositeCentroid_vsub_point_eq_smul_vsub, smul_smul,one_div,mul_assoc,
      inv_mul_cancel₀ (by norm_cast), mul_one]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

theorem median_eq_affineSpan_point_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.median i = affineSpan k {s.points i, s.centroid} := by
  have h1 : s.median i ≤ affineSpan k {s.points i, s.centroid} := by
    unfold median
    apply affineSpan_pair_le_of_right_mem
    have h : s.faceOppositeCentroid i = (-1 / (n:k)) • (s.points i -ᵥ s.centroid) +ᵥ s.centroid
        := by
      rw[point_eq_smul_vsub_vadd_centroid, vadd_vsub, smul_smul]
      field_simp
      rw [div_mul_cancel₀ _ (NeZero.ne (n:k)), neg_one_smul,neg_neg, vsub_vadd]
    rw [h]
    exact smul_vsub_rev_vadd_mem_affineSpan_pair _ _ _
  have h2 : affineSpan k {s.points i, s.centroid} ≤ s.median i := by
    rw [median]
    apply affineSpan_pair_le_of_right_mem
    exact centroid_mem_median s i
  exact le_antisymm h1 h2




theorem mem_median_eq_linemap [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
    {p : P} (h : p ∈ s.median i) :
    ∃ (r : k),
    p = AffineMap.lineMap (s.faceOppositeCentroid i) (s.points i) r := by
  rw [median] at h
  set v := p -ᵥ s.faceOppositeCentroid i
  have hp: p = v +ᵥ s.faceOppositeCentroid i := by rw [vsub_vadd]
  rw [hp] at h

  rw [vadd_right_mem_affineSpan_pair] at h
  choose r hr using h
  use r
  rw [AffineMap.lineMap_apply]
  rw [hr]
  simp_rw [hp]


theorem mem_median_eq_smul_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
    {p : P} (h : p ∈ s.median i) :
    ∃ (r : k), p = r • (s.faceOppositeCentroid i -ᵥ s.points i) +ᵥ s.points i := by
  rw [median_eq_affineSpan_point_centroid] at h


  sorry

open Function

variable {ι : Type*}

theorem linearIndepdent_point_vsub_centroid [CharZero k] (s : Simplex k P n) :
  LinearIndependent k (fun i => s.points i -ᵥ s.centroid) := by
  -- 展开线性无关的定义
  rw [linearIndependent_iff']

  intro fs g hg i hi


  -- exact s.independent fs g
  sorry



theorem affineIndependent_iff_linearIndependent_vsub' (p : ι → P) (i1 : ι) :
    AffineIndependent k p → LinearIndependent k fun i : { x // x ≠ i1 } => (p i -ᵥ p i1 : V) := by
  classical
    intro h
    rw [linearIndependent_iff']
    intro s g hg i hi
    set f : ι → k := fun x => if hx : x = i1 then -∑ y ∈ s, g y else g ⟨x, hx⟩ with hfdef
    let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
    have hfg : ∀ x : { x // x ≠ i1 }, g x = f x := by grind
    rw [hfg]
    have hf : ∑ ι ∈ s2, f ι = 0 := by
      rw [Finset.sum_insert
          (Finset.notMem_map_subtype_of_not_property s (Classical.not_not.2 rfl)),
        Finset.sum_subtype_map_embedding fun x _ => (hfg x).symm]
      rw [hfdef]
      dsimp only
      rw [dif_pos rfl]
      exact neg_add_cancel _

    have hs2 : s2.weightedVSub p f = (0 : V) := by
      set f2 : ι → V := fun x => f x • (p x -ᵥ p i1) with hf2def
      set g2 : { x // x ≠ i1 } → V := fun x => g x • (p x -ᵥ p i1)
      have hf2g2 : ∀ x : { x // x ≠ i1 }, f2 x = g2 x := by
        simp only [g2, hf2def]
        refine fun x => ?_
        rw [hfg]
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s2 f p hf (p i1),
        Finset.weightedVSubOfPoint_insert, Finset.weightedVSubOfPoint_apply,
        Finset.sum_subtype_map_embedding fun x _ => hf2g2 x]
      exact hg

    exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))


-- theorem mem_median_exist_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1))
--     {p : P} (h : p ∈ s.median i) :
--     ∃ (r : k),  s.points i -ᵥ p = r • (s.centroid -ᵥ s.points i) := by
--     sorry

/-- The medians of a simplex are concurrent at the centroid of the simplex -/
theorem eq_centroid_of_forall_mem_median [CharZero k] (s : Simplex k P n) {hn : 2 ≤ n} {p : P}
    (h : ∀ i, p ∈ s.median i) :
    p = s.centroid := by

  rw [←vsub_eq_zero_iff_eq]

  set v := p -ᵥ s.centroid
  have hp : p = v +ᵥ s.centroid := by rw [vsub_vadd]
  conv at h =>
    intro i
    rw [median_eq_affineSpan_point_centroid]
    rw [hp]
    rw [vadd_right_mem_affineSpan_pair]

  let u : Fin (n + 1) → V := fun i => s.points i -ᵥ s.centroid
  have h_span : ∀ i, v ∈ (Submodule.span k ({u i} : Set V)) := by
    intro i
    unfold u
    unfold v
    sorry

  have hi : LinearIndependent k u :=by
    sorry

  have he : ∃ i j : Fin (n + 1), i ≠ j := by
    use 0 , 1
    norm_num
  choose i j hij using he

  have h_ij : Disjoint ({i}: Set (Fin (n+1))) {j} := by
    simp [hij]

  set u_i := Submodule.span k ({u i} : Set V)
  set u_j := Submodule.span k ({u j} : Set V)
  have h_disjoint : Disjoint u_i u_j := by
    have x:= LinearIndependent.disjoint_span_image hi h_ij
    simp at x
    exact x


  have h_vi : v ∈ u_i := by
    apply h_span
  have h_vj : v ∈ u_j := by
    apply h_span

  exact Submodule.disjoint_def.1 h_disjoint _ h_vi h_vj










  -- rw [centroid_iff_sum_vsub_eq_zero]





end Simplex

end Affine

namespace EuclideanGeometry

open RealInnerProductSpace Finset Affine EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable {n : ℕ} [NeZero n]

theorem dist_point_centroid (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    dist (s.points i) s.centroid = n * dist s.centroid (s.faceOppositeCentroid i) := by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_centroid_eq_smul_vsub i, norm_smul, Real.norm_natCast]

theorem dist_point_faceOppositeCentroid (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    dist (s.points i) (s.faceOppositeCentroid i) = (n+1)
    * dist s.centroid (s.faceOppositeCentroid i) := by
  simp_rw [dist_eq_norm_vsub, s.point_vsub_faceOppositeCentroid_eq_smul_vsub i,
    norm_smul]
  norm_cast

end EuclideanGeometry

namespace Affine

namespace Triangle

open EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem dist_point_centroid (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist (t.points i) t.centroid = 2 * dist t.centroid (t.faceOppositeCentroid i) := by
  field_simp [EuclideanGeometry.dist_point_centroid]

theorem dist_point_faceOppositeCentroid (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist (t.points i) (t.faceOppositeCentroid i) = 3 * dist t.centroid (t.faceOppositeCentroid i)
    := by
  rw [EuclideanGeometry.dist_point_faceOppositeCentroid]
  norm_cast

end Triangle

end Affine

end
