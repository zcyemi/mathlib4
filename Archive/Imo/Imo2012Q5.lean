import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Triangle

import Mathlib.Tactic


open Affine Affine.Simplex EuclideanGeometry Module

open scoped Affine EuclideanGeometry Real


attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]


namespace Imo2012Q5

noncomputable section

-- Lemmas from test.lean

open RealInnerProductSpace


structure Imo2012Q5Cfg where
  (A B C D X K L M : Pt)
  affine_indep_ABC : AffineIndependent ℝ ![A, B, C]
  triangle_ABC : Triangle ℝ Pt := ⟨![A, B, C], affine_indep_ABC⟩
  angle_BCA : ∠ B C A = π / 2
  D_eq_altitudeFoot : D = triangle_ABC.altitudeFoot 2
  Sbtw_CXD : Sbtw ℝ C X D
  Sbtw_AKX : Sbtw ℝ A K X
  BK_eq_BC : dist B K = dist B C
  Sbtw_BLX : Sbtw ℝ B L X
  AL_eq_AC : dist A L = dist A C
  M_mem_inf_AL_BK : M ∈ line[ℝ, A, L] ⊓ line[ℝ, B, K]

namespace Imo2012Q5Cfg

section lemmas

open EuclideanGeometry Real
open Affine Module
open scoped EuclideanGeometry
open scoped RealInnerProductSpace

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

section affineCombination

open Finset
open Module Affine Simplex EuclideanGeometry Real
open AffineMap
variable {ι k V P : Type*} [Fintype ι] [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

theorem weight_lineMap_of_affineCombination_lineMap {p : ι → P}
    (h_indep: AffineIndependent k p)
    {q₁ q₂ q₃ : P}
    {w₁ w₂ w₃ : ι → k}
    (hq₁ : q₁ = affineCombination k univ p w₁)
    (hq₂ : q₂ = affineCombination k univ p w₂)
    (hq₃ : q₃ = affineCombination k univ p w₃)
    (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1) (hw₃ : ∑ i, w₃ i = 1)
    {c : k}
    (hline : q₂ = (AffineMap.lineMap q₁ q₃) c)  :
    ∀ i, w₂ i = lineMap (w₁ i) (w₃ i) c := by

  set b := q₁

  have h1:= sum_smul_vsub_const_eq_affineCombination_vsub univ w₁ p b hw₁
  have h2:= sum_smul_vsub_const_eq_affineCombination_vsub univ w₂ p b hw₂
  have h3:= sum_smul_vsub_const_eq_affineCombination_vsub univ w₃ p b hw₃

  have hline_vsub := lineMap_vsub q₁ q₃ b c
  rw [← hline, lineMap_apply] at hline_vsub
  rw [← hq₁] at h1
  rw [← hq₂] at h2
  rw [← hq₃] at h3

  rw [← h1, ← h2, ← h3, eq_vadd_iff_vsub_eq] at hline_vsub

  simp_rw [vsub_eq_sub, smul_sub, smul_sum, ← Finset.sum_sub_distrib] at hline_vsub
  conv_lhs at hline_vsub =>
    enter [2]
    ext x
    rw [← sub_smul]
  conv_rhs at hline_vsub =>
    enter [2]
    ext x
    rw [← smul_sub, ← sub_smul, smul_smul]
  apply sub_eq_zero.mpr at hline_vsub
  rw [←sum_sub_distrib] at hline_vsub
  conv_lhs at hline_vsub =>
    enter [2]
    ext x
    rw [← sub_smul]
  set f := fun x => (w₂ x - w₁ x - c * (w₃ x - w₁ x)) with f_def
  have hf : ∀ (x : ι), f x = (w₂ x - w₁ x - c * (w₃ x - w₁ x)) :=by aesop
  conv_lhs at hline_vsub =>
    enter [2]
    ext x
    rw [←hf x]
  unfold AffineIndependent at h_indep
  have hf_sum: ∑ i, f i = 0 := by
    simp_rw [f_def]
    conv_lhs =>
      enter [2]
      ext x
      rw [mul_sub, ← sub_add]
    simp_rw [sum_add_distrib, sum_sub_distrib, ←mul_sum]
    rw [hw₂, hw₁, hw₃]
    simp

  have h2 := h_indep (Finset.univ) f hf_sum
  rw [weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hf_sum b, weightedVSubOfPoint_apply] at h2
  have h3:= h2 hline_vsub
  simp_rw [f_def] at h3
  conv =>
     enter [2]
     rw [lineMap_apply]
  intro i
  have h4 := h3 i
  simp at h4
  rw [sub_eq_iff_eq_add,sub_eq_iff_eq_add] at h4
  simp_rw [h4, zero_add]
  rfl

end affineCombination

@[simp]
theorem AffineIndependent_reverse (a b c: Pt) (h: AffineIndependent ℝ ![a,b,c]) :
  AffineIndependent ℝ ![c,b,a] := by
  rw [←affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert h using 1
  ext x
  fin_cases x <;> rfl

@[simp]
theorem AffineIndependent_comm_left {a b c: Pt} (h: AffineIndependent ℝ ![a,b,c]) :
  AffineIndependent ℝ ![b,a,c] := by
  rw [←affineIndependent_equiv (Equiv.swap (0 : Fin 3) 1)]
  convert h using 1
  ext x
  fin_cases x <;> rfl

@[simp]
theorem AffineIndependent_comm_right {a b c: Pt} (h: AffineIndependent ℝ ![a,b,c]) :
  AffineIndependent ℝ ![a,c,b] := by
  rw [←affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert h using 1
  ext x
  fin_cases x <;> rfl

theorem collinear_comm_left {p₁ p₂ p₃ : Pt}
  (h: Collinear ℝ {p₁, p₂, p₃}):
  Collinear ℝ {p₂, p₁, p₃} := by
  rw [Set.insert_comm]
  exact h

theorem collinear_reverse {p₁ p₂ p₃ : Pt}
  (h: Collinear ℝ {p₁, p₂, p₃}):
  Collinear ℝ {p₃, p₂, p₁} := by
  rw [Set.insert_comm]
  rw [Set.pair_comm]
  rw [Set.insert_comm]
  exact h

theorem collinear_comm_right {p₁ p₂ p₃ : Pt}
  (h: Collinear ℝ {p₁, p₂, p₃}):
  Collinear ℝ {p₁, p₃, p₂} := by
  rw [Set.pair_comm]
  exact h


theorem SAS_eq_angle (a b c : Pt) (a' b' c' : Pt) (h_abc : ∠ a b c = ∠ a' b' c')
  (h_dist : dist a b * dist c' b' = dist c b * dist a' b')
  (h_not_collinear_abc : ¬ Collinear ℝ ({a, b, c} : Set Pt))
  (h_not_collinear_a'b'c' : ¬ Collinear ℝ ({a', b', c'} : Set Pt)) :
  ∠ c a b = ∠ c' a' b' ∧ ∠ b c a = ∠ b' c' a' := by
  have hab : a ≠ b := ne₁₂_of_not_collinear h_not_collinear_abc
  have hbc : b ≠ c := ne₂₃_of_not_collinear h_not_collinear_abc
  have ha'b' : a' ≠ b' := ne₁₂_of_not_collinear h_not_collinear_a'b'c'
  have hb'c' : b' ≠ c' := ne₂₃_of_not_collinear h_not_collinear_a'b'c'
  have h_sinabc : Real.sin (∠ a b c) = Real.sin (∠ a' b' c') := by
    rw [h_abc]
  obtain h1 := sin_angle_div_dist_eq_sin_angle_div_dist hbc.symm hab.symm
  obtain h2 := (sin_angle_div_dist_eq_sin_angle_div_dist hb'c'.symm ha'b'.symm).symm
  have h1_mul_h2 : (sin (∠ a c b) * sin (∠ b' a' c')) / (dist b a * dist c' b') =
  (sin (∠ b a c) * sin (∠ a' c' b')) / ( dist c b * dist b' a') := by
    calc
    _ = (sin (∠ b a c) / dist c b) * (sin (∠ a' c' b') / dist b' a') := by
      rw[← h1, ← h2]
      ring
    _ = (sin (∠ b a c) * sin (∠ a' c' b')) / ( dist c b * dist b' a') := by
      ring
  rw [dist_comm] at h_dist
  nth_rw 4 [dist_comm] at h_dist
  rw [h_dist, div_left_inj'] at h1_mul_h2
  swap
  apply mul_ne_zero
  exact dist_ne_zero.mpr (id (Ne.symm hbc))
  exact dist_ne_zero.mpr (id (Ne.symm ha'b'))
  have h3 : ∠ b a c = π - (∠ b c a + ∠ a b c) := by
    obtain h := angle_add_angle_add_angle_eq_pi c hab.symm
    rw[← h, angle_comm]
    ring
  have h4 : ∠ b' a' c' = π - (∠ b' c' a' + ∠ a b c) := by
    obtain h := angle_add_angle_add_angle_eq_pi c' ha'b'.symm
    rw[← h, angle_comm, h_abc]
    ring
  rw[h3, h4, sin_pi_sub, sin_pi_sub, sin_add, sin_add] at h1_mul_h2
  apply sub_eq_zero_of_eq at h1_mul_h2
  have h : sin (∠ a b c) * sin (∠ b c a - ∠ b' c' a') = 0 := by
    calc
    _ = sin (∠ a b c) * (sin (∠ b c a) * cos (∠ b' c' a') - cos (∠ b c a) * sin (∠ b' c' a'))
      + cos (∠ a b c) * (sin (∠ b c a) * sin (∠ b' c' a') - sin (∠ b c a) * sin (∠ b' c' a')):= by
      simp only [sub_self, mul_zero, add_zero, mul_eq_mul_left_iff]
      left
      rw[sin_sub]
    _ = 0 := by
      rw[← h1_mul_h2, mul_sub, mul_sub, mul_add, add_mul]
      have h₁ : sin (∠ a b c) * (sin (∠ b c a) * cos (∠ b' c' a')) = sin (∠ a c b) * (cos (∠ b' c' a') * sin (∠ a b c)) := by
        rw[mul_comm, mul_assoc, angle_comm]
      have h₂ : sin (∠ a b c) * (cos (∠ b c a) * sin (∠ b' c' a')) = cos (∠ b c a) * sin (∠ a b c) * sin (∠ a' c' b') := by
        rw[mul_comm, mul_assoc]
        nth_rw 2 [angle_comm, mul_comm]
        rw[← mul_assoc]
      have h₃ : cos (∠ a b c) * (sin (∠ b c a) * sin (∠ b' c' a')) = sin (∠ a c b) * (sin (∠ b' c' a') * cos (∠ a b c)) := by
        rw[mul_comm, mul_assoc, angle_comm]
      have h₄ : cos (∠ a b c) * (sin (∠ b c a) * sin (∠ b' c' a')) = sin (∠ b c a) * cos (∠ a b c) * sin (∠ a' c' b') := by
        rw[mul_comm, mul_assoc]
        nth_rw 2 [angle_comm, mul_comm]
        rw[← mul_assoc]
      rw[h₁, h₂]
      nth_rw 1[h₃]
      rw[h₄]
      ring
  have h_sinc : sin (∠ b c a - ∠ b' c' a') = 0 := by
    have h_ne_zero : sin (∠ a b c) ≠ 0 := by
      exact sin_ne_zero_of_not_collinear h_not_collinear_abc
    exact (mul_eq_zero_iff_left h_ne_zero).mp h
  have h_bca : ∠ b c a - ∠ b' c' a' = 0 := by
    have h_not_collinear_bca : ¬ Collinear ℝ ({b, c, a} : Set Pt) := by
      rw[← affineIndependent_iff_not_collinear_set] at *
      apply AffineIndependent_reverse
      apply AffineIndependent_comm_right
      exact h_not_collinear_abc
    have h_not_collinear_b'c'a' : ¬ Collinear ℝ ({b', c', a'} : Set Pt) := by
      rw[← affineIndependent_iff_not_collinear_set] at *
      apply AffineIndependent_reverse
      apply AffineIndependent_comm_right
      exact h_not_collinear_a'b'c'
    have h_range : 0 < ∠ b c a ∧ ∠ b c a < π := by
      constructor
      refine angle_pos_of_not_collinear ?_
      exact h_not_collinear_bca
      apply angle_lt_pi_of_not_collinear
      exact h_not_collinear_bca
    have h_range' : 0 < ∠ b' c' a' ∧ ∠ b' c' a' < π := by
      constructor
      refine angle_pos_of_not_collinear ?_
      exact h_not_collinear_b'c'a'
      apply angle_lt_pi_of_not_collinear
      exact h_not_collinear_b'c'a'
    have h_diff_range : -π < ∠ b c a - ∠ b' c' a' ∧ ∠ b c a - ∠ b' c' a' < π := by
      constructor
      linarith
      linarith
    rw [← sin_eq_zero_iff_of_lt_of_lt]
    exact h_sinc
    exact h_diff_range.left
    exact h_diff_range.right

  rw[sub_eq_zero] at h_bca
  rw[h_bca, ← h4, angle_comm] at h3
  nth_rw 2 [angle_comm] at h3
  exact ⟨h3, h_bca⟩

theorem affineIndependent_of_affineIndependent_collinear {a b c d: Pt}
  (hABC: AffineIndependent ℝ ![a,b,c])
  (hd: Collinear ℝ {b, c, d})
  (hbd: b ≠ d):
  AffineIndependent ℝ ![a, b, d] := by
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have h_abcd: Collinear ℝ {a, c, b, d} := by
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hbd
    · apply Collinear.mem_affineSpan_of_mem_of_ne hd (by simp) (by simp) (by simp) hbd
  have h_abc: Collinear ℝ {a, b, c} := by
    apply Collinear.subset _ h_abcd
    intro x hx
    simp at hx
    tauto
  rw [affineIndependent_iff_not_collinear_set] at hABC
  exact hABC h_abc

theorem affineIndependent_of_sbtw_affineIndependent'
  {a b c d: Pt}
  (hADC: AffineIndependent ℝ ![a,d,c])
  (hd: Sbtw ℝ a d b) :
  AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  have h_collinear: Collinear ℝ {a, d, b} := by
    have h:= hd.wbtw.collinear
    apply Collinear.subset _ h
    intro x hx
    simp at hx
    tauto
  have h_indep: AffineIndependent ℝ ![c, a, d] := by simp [hADC]
  have h_ad: a ≠ b:= hd.left_ne_right
  have h:= affineIndependent_of_affineIndependent_collinear h_indep h_collinear h_ad
  have : AffineIndependent ℝ ![a, b, c] := by simp [h]
  rw [←affineIndependent_iff_not_collinear_set]
  exact this

theorem angle_eq_of_sbtw {A B P C : Pt} (h : Sbtw ℝ B P C):
  ∠ A B P = ∠ A B C := by
  rw [EuclideanGeometry.angle]
  rw [EuclideanGeometry.angle]
  have h : ∃ r : ℝ, 0 < r ∧ (P -ᵥ B) = r • (C -ᵥ B) := by
    have hr := sbtw_iff_mem_image_Ioo_and_ne.mp h
    obtain ⟨hr1, hr2⟩ := hr
    simp at hr1
    obtain ⟨r, hr1, hr2⟩ := hr1
    rw [AffineMap.lineMap_apply] at hr2
    use r; repeat aesop
  obtain ⟨r, hr1,hr2⟩ := h
  rw [hr2]
  apply InnerProductGeometry.angle_smul_right_of_pos
  exact hr1

theorem oangle_eq_or_eq_neg_of_angle_eq [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
    {p₁ p₂ p₃ p₄ p₅ p₆ : Pt} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
    (h1 : p₂ ≠ p₁) (h2 : p₂ ≠ p₃) (h3 : p₅ ≠ p₄) (h4 : p₅ ≠ p₆) :
    ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ ∨ ∡ p₁ p₂ p₃ = - ∡ p₄ p₅ p₆ := by
  have h_1 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h1.symm h2.symm
  have h_2 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h3.symm h4.symm
  rcases h_1 with h₁ | h₁ <;> rcases h_2 with h₂ | h₂
  · left
    rw[h₁, h₂, h]
  · right
    rw[h₁, h₂, h, neg_neg]
  · right
    rw[h₁, h₂, h]
  · left
    rw[h₁, h₂, h]

theorem oangle_ne_zero_and_ne_pi_iff_not_collinear {p₁ p₂ p₃ : Pt}
  [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] :
  ∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π ↔ ¬ Collinear ℝ {p₁, p₂, p₃} := by
  rw[oangle_ne_zero_and_ne_pi_iff_affineIndependent, affineIndependent_iff_not_collinear_set]

theorem cospherical_of_mul_dist_eq_mul_dist
    [Fact (finrank ℝ V = 2)] [ho: Oriented ℝ V (Fin 2)]
    {a b c d p : Pt} (h_notCollinear : ¬ Collinear ℝ ({a, p, c} : Set Pt))
    (hapb : Sbtw ℝ a p b) (hcpd : Sbtw ℝ c p d)
    (h : dist a p * dist b p = dist c p * dist d p) :
    Cospherical ({a, b, c, d} : Set Pt) := by
  have h_notCollinear_pca : ¬Collinear ℝ {p, c, a} := by
    rw[← affineIndependent_iff_not_collinear_set] at *
    apply AffineIndependent_comm_left
    apply AffineIndependent_reverse
    exact h_notCollinear

  have d_ne_p : d ≠ p := hcpd.right_ne
  have b_ne_p : b ≠ p := hapb.right_ne

  have h_notCollinear_apd : AffineIndependent ℝ ![a, p, d] := by
    rw[← affineIndependent_iff_not_collinear_set] at *
    apply affineIndependent_of_affineIndependent_collinear
    exact h_notCollinear
    apply collinear_comm_left
    exact hcpd.wbtw.collinear
    exact d_ne_p.symm

  have h_notCollinear_abd : ¬ Collinear ℝ ({a, b, d} : Set Pt) := by
    rw[← affineIndependent_iff_not_collinear_set] at *
    apply affineIndependent_of_sbtw_affineIndependent'
    exact h_notCollinear_apd
    exact hapb


  have h_notCollinear_dpb: ¬Collinear ℝ {d, p, b} := by
    rw[← affineIndependent_iff_not_collinear_set] at *
    apply AffineIndependent_reverse at h_notCollinear_apd
    apply affineIndependent_of_affineIndependent_collinear
    exact h_notCollinear_apd
    apply collinear_comm_left
    exact hapb.wbtw.collinear
    exact b_ne_p.symm

  have a_ne_c : a ≠ c := ne₁₃_of_not_collinear h_notCollinear
  have b_ne_d : b ≠ d := ne₂₃_of_not_collinear h_notCollinear_abd
  have a_ne_p : a ≠ p := hapb.left_ne
  have c_ne_p : c ≠ p := hcpd.left_ne

  have h_angle : ∡ a p c = ∡ b p d := _root_.Sbtw.oangle_eq_left_right hapb hcpd

  have h1: ∠ a p c = ∠ d p b := by
    nth_rw 2[angle_comm]
    apply angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi
    exact Sbtw.angle₁₂₃_eq_pi hapb
    exact Sbtw.angle₁₂₃_eq_pi hcpd

  obtain h_angle_eq := SAS_eq_angle a p c d p b h1 h h_notCollinear h_notCollinear_dpb

  have h2:= h_angle_eq.right
  rw[angle_comm] at h2
  nth_rw 2[angle_comm] at h2

  have h3 := h_angle_eq.left
  rw[angle_comm] at h3
  nth_rw 2[angle_comm] at h3

  apply EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear

  have hoangle : ∡ a b d = ∡ a c d := by
    have h₁ : ∡ a b d = ∡ p b d := by
      symm
      apply _root_.Sbtw.oangle_eq_left
      exact hapb.symm
    have h₂ : ∡ a c d = ∡ a c p := by
      symm
      apply _root_.Sbtw.oangle_eq_right
      exact hcpd
    rw [h₁, h₂]
    apply oangle_eq_of_angle_eq_of_sign_eq
    rw[h2, angle_comm]
    have h_apc : ∡ a p c + ∡ p c a + ∡ c a p = π := by
      exact oangle_add_oangle_add_oangle_eq_pi a_ne_p.symm c_ne_p a_ne_c
    have h_bpd : ∡ b p d + ∡ p d b + ∡ d b p = π := by
      exact oangle_add_oangle_add_oangle_eq_pi b_ne_p.symm d_ne_p b_ne_d
    rw[← h_apc, h_angle, add_assoc, add_assoc] at h_bpd
    simp at h_bpd
    have h2_oangle : ∡ a c p = ∡ p b d ∨ ∡ a c p = - ∡ p b d := by
      nth_rw 2[angle_comm] at h2
      exact oangle_eq_or_eq_neg_of_angle_eq h2 a_ne_c.symm c_ne_p b_ne_p b_ne_d
    rcases h2_oangle with h2_oangle | h2_oangle_neg
    · rw[h2_oangle]
    · have h4 : -∡ p b d = ∡ d b p := by
        symm
        exact oangle_rev p b d
      rw [← h2_oangle_neg] at h4
      rw[← h4] at h_bpd
      have h3_oangle : ∡ p a c = ∡ p d b ∨ ∡ p a c = - ∡ p d b := by
        exact oangle_eq_or_eq_neg_of_angle_eq h3 a_ne_p a_ne_c d_ne_p b_ne_d.symm
      rcases h3_oangle with h3_oangle | h3_oangle_neg
      · exfalso
        have h₃ : - ∡ c a p = ∡ p a c := by
          symm
          exact oangle_rev c a p
        have h₄ : ∡ a c p = - ∡ p c a := oangle_rev p c a
        rw[← h3_oangle, ← h₃, h₄] at h_bpd
        have h₅ : -∡ c a p + -∡ p c a = - (∡ p c a + ∡ c a p) := by
          simp only [neg_add_rev]
        rw[h₅] at h_bpd
        have h₆ : (2 : ℤ) • (∡ p c a + ∡ c a p) = 0 := by
          rw[neg_eq_iff_add_eq_zero, ← two_zsmul] at h_bpd
          exact h_bpd
        rw[Angle.two_zsmul_eq_zero_iff] at h₆
        have h₇ : ∡ a p c ≠ 0 ∧ ∡ a p c ≠ π := by
          rw[oangle_ne_zero_and_ne_pi_iff_not_collinear]
          exact h_notCollinear
        rcases h₆ with h₆ | h₆
        · rw[add_assoc, h₆, add_zero] at h_apc
          aesop
        · rw[add_assoc, h₆] at h_apc
          simp at h_apc
          aesop
      · exfalso
        rw[← neg_eq_iff_eq_neg] at h3_oangle_neg h2_oangle_neg
        have h₃ : ∡ c a p = -∡ p a c := oangle_rev p a c
        have h₄ : ∡ a c p = -∡ p c a := oangle_rev p c a
        rw[← h3_oangle_neg, ← h₃, h₄, add_comm] at h_bpd
        simp at h_bpd
        have h₅ : (2 : ℤ) • ∡ p c a = 0 := by
          rw[neg_eq_iff_add_eq_zero, ← two_zsmul] at h_bpd
          exact h_bpd
        rw[Angle.two_zsmul_eq_zero_iff] at h₅
        have h₆ : ∡ p c a ≠ 0 ∧ ∡ p c a ≠ π := by
          rw[oangle_ne_zero_and_ne_pi_iff_not_collinear]
          exact h_notCollinear_pca
        rcases h₅ with h₅ | h₅
        · aesop
        · rw[add_comm, h₅] at h_apc
          aesop
  rw [hoangle]
  exact h_notCollinear_abd

theorem angle_point_altitudeFoot_eq_pi_div_two (t : Affine.Triangle ℝ Pt)
    {i j: Fin 3} (h : i ≠ j) :
    angle (t.points i) (t.altitudeFoot i) (t.points j) = π / 2 := by
  have h : ⟪t.points j -ᵥ t.altitudeFoot i, t.points i -ᵥ t.altitudeFoot i⟫ = 0 := by
    refine Submodule.inner_right_of_mem_orthogonal
      (K := vectorSpan ℝ (t.points '' {i}ᶜ))
      (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
        (t.mem_affineSpan_image_iff.2 h.symm)
        (Affine.Simplex.altitudeFoot_mem_affineSpan_image_compl _ _))
      ?_
    rw [← direction_affineSpan, ← Affine.Simplex.range_faceOpposite_points]
    exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

  unfold  EuclideanGeometry.angle
  rw [InnerProductGeometry.angle_comm]
  exact (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp h

theorem sbtw_altitudeFoot_of_rightAngled {t : Affine.Triangle ℝ Pt}
    {i j k : Fin 3}
    (hij: i ≠ j) (hjk: j ≠ k) (hki: k ≠ i)
    (h_angle : angle (t.points i) (t.points j) (t.points k) = π / 2):
    Sbtw ℝ (t.points i) (t.altitudeFoot j) (t.points k) := by
  have not_col : ¬ Collinear ℝ { t.points i, t.points j, t.points k } := by
    rw [← affineIndependent_iff_not_collinear_set]
    have h_set : {i, j, k} = (Finset.univ : Finset (Fin 3)) := by grind
    have f_inj: Function.Injective ![i, j, k] :=by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp at hxy <;> grind
    set f : Fin 3 ↪ Fin 3 := { toFun := ![i, j, k], inj' := f_inj } with f_def

    have h: ![t.points i, t.points j, t.points k] = t.points ∘ f := by
      ext x
      fin_cases x <;> simp [f_def]
    rw [h]
    have h_indep := t.independent
    apply h_indep.comp_embedding

  have h_col : Collinear ℝ { t.points i, t.altitudeFoot j,t.points k} := by
    have h:= t.altitudeFoot_mem_affineSpan_faceOpposite j
    have h1: Set.range (t.faceOpposite j).points = {t.points i, t.points k} :=by
      rw [Simplex.range_faceOpposite_points]
      have h2: {i, k} = ({j} : Set (Fin 3))ᶜ := by grind
      rw [← h2]
      grind
    rw [h1] at h
    rw [Set.insert_comm]
    apply collinear_insert_of_mem_affineSpan_pair
    exact h

  have h1 := Collinear.wbtw_or_wbtw_or_wbtw h_col

  set D:= t.altitudeFoot j with D_def
  set I:= t.points i with I_def
  set J:= t.points j with J_def
  set K:= t.points k with K_def

  have angle_JDI : angle J D I = π / 2 := by
    rw [D_def]
    exact angle_point_altitudeFoot_eq_pi_div_two t hij.symm

  have angle_JDK : angle J D K= π / 2 := by
    rw [D_def]
    exact angle_point_altitudeFoot_eq_pi_div_two t hjk

  have dist_DK_sq := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two J D K).mpr angle_JDK
  have dist_DI_sq := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two J D I).mpr angle_JDI
  have dist_IK_sq := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two I J K).mpr h_angle
  simp_rw [← pow_two] at dist_DK_sq dist_IK_sq dist_DI_sq
  rw [dist_comm J I] at dist_DI_sq

  have ne_IJ : I ≠ J := ne₁₂_of_not_collinear not_col
  have ne_JK : J ≠ K := ne₂₃_of_not_collinear not_col
  have ne_IK : I ≠ K := ne₁₃_of_not_collinear not_col

  have D_ne_I : D ≠ I := by
    intro h
    rw [← h] at h_angle
    have h_sum:= EuclideanGeometry.angle_add_angle_add_angle_eq_pi D ne_JK
    rw [angle_JDK,angle_comm, h_angle] at h_sum
    simp at h_sum
    have h_sum_ne : ∠ D K J ≠ 0 := by
      apply angle_ne_zero_of_not_collinear
      rw[← affineIndependent_iff_not_collinear_set] at *
      apply AffineIndependent_reverse
      apply AffineIndependent_comm_left at not_col
      apply AffineIndependent_comm_right at not_col
      apply collinear_comm_right at h_col
      apply collinear_comm_left at h_col
      apply affineIndependent_of_affineIndependent_collinear
      exact not_col
      exact h_col
      rw[← h] at ne_IK
      exact ne_IK.symm
    apply h_sum_ne at h_sum
    exact h_sum

  have h_D_ne_right : D ≠ K := by
    intro h
    rw [← h, angle_comm] at h_angle
    have h_sum:= EuclideanGeometry.angle_add_angle_add_angle_eq_pi D ne_IJ
    rw [angle_comm] at angle_JDI
    rw [angle_JDI,angle_comm, h_angle, add_assoc] at h_sum
    simp at h_sum
    have h_sum_ne : ∠ D I J ≠ 0 := by
      apply angle_ne_zero_of_not_collinear
      rw[← affineIndependent_iff_not_collinear_set] at *
      apply AffineIndependent_reverse
      apply AffineIndependent_comm_left at not_col
      apply collinear_comm_right at h_col
      apply affineIndependent_of_affineIndependent_collinear
      exact not_col
      exact h_col
      rw[← h] at ne_IK
      exact ne_IK
    apply h_sum_ne at h_sum
    exact h_sum

  have dist_DK_lt : dist K D ^ 2  < dist I K ^ 2 := by
    have h_JD : 0 < dist J D ^ 2 := by
      apply pow_two_pos_of_ne_zero
      rw [dist_ne_zero]
      aesop
    calc  _ < dist K D ^ 2 + dist J D ^ 2 := by linarith
          _ = dist J K ^ 2 := by linarith
          _ = dist K J ^ 2 := by rw [dist_comm J K]
    rw [dist_IK_sq]
    apply lt_add_of_pos_left
    apply pow_two_pos_of_ne_zero
    rw [dist_ne_zero]
    exact ne_IJ
  rw [pow_lt_pow_iff_left₀ (by simp) (by simp) (by simp)] at dist_DK_lt

  have dist_DI_lt : dist I D ^ 2  < dist I K ^ 2 := by
    have h_JD : 0 < dist J D ^ 2 := by
      apply pow_two_pos_of_ne_zero
      rw [dist_ne_zero]
      aesop
    calc  _ < dist J D ^ 2 + dist I D ^ 2 := by linarith
          _ = dist I J ^ 2 := by linarith
          _ = dist J I ^ 2 := by rw [dist_comm I J]
    rw [dist_IK_sq]
    rw [dist_comm J I]
    apply lt_add_of_pos_right
    apply pow_two_pos_of_ne_zero
    rw [dist_ne_zero]
    exact ne_JK.symm
  rw [pow_lt_pow_iff_left₀ (by simp) (by simp) (by simp)] at dist_DI_lt

  rcases h1 with h1 | h1 | h1
  · exact ⟨h1, D_ne_I, h_D_ne_right⟩
  · have := h1.dist_add_dist
    have h2: dist I K < dist D I := by
      rw [← this]
      rw [dist_comm I K]
      apply lt_add_of_pos_left
      rw [dist_pos]
      exact h_D_ne_right
    rw [dist_comm D I] at h2
    linarith
  · have := h1.dist_add_dist
    have h2: dist K I < dist K D := by
      rw [← this]
      apply lt_add_of_pos_right
      rw [dist_pos]
      exact D_ne_I.symm
    rw [dist_comm K I] at h2
    linarith

theorem Triangle.mem_interior_of_sbtw_sbtw {P Q : Pt}
  (t : Triangle ℝ Pt)
  {i j k : Fin 3}
  (h_ij : i ≠ j)
  (h_jk : j ≠ k)
  (h_ki : k ≠ i)
  (hQ: Sbtw ℝ (t.points j) Q (t.points k))
  (hP: Sbtw ℝ (t.points i) P Q) :
  P ∈ t.interior := by
  sorry

theorem Simplex.notMem_affineSpan_faceOpposite_of_mem_interior {n:ℕ} [NeZero n] (s: Simplex ℝ Pt n)
    (i : Fin (n + 1)) {x : Pt} (hx : x ∈ s.interior) :
  x ∉ affineSpan ℝ (Set.range (s.faceOpposite i).points) := by
  have zoer_lt: 0 < n := by
    have := NeZero.ne n
    positivity
  set fs := Finset.univ \ {i} with fs_def
  have fs_card : fs.card = n - 1 + 1 := by
    rw [Nat.sub_add_cancel (by grind)]
    rw [fs_def]
    rw [Finset.card_sdiff]
    simp
  have h_lt : n - 1 < n := by aesop
  intro h_mem_face
  have h_mem : x ∈ affineSpan ℝ (Set.range s.points) := by
    have hx1:= hx
    rcases hx1 with ⟨w, hw, ⟨_, hx2⟩⟩
    rw [← hx2]
    apply affineCombination_mem_affineSpan hw
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype h_mem with ⟨w_P, hw_P, h_comb⟩
  have hw_P' : ∑  i ∈ Finset.univ, w_P i = 1 := by grind
  have h_mem_face' : x ∈ affineSpan ℝ (s.points '' fs) := by
    rw [Affine.Simplex.range_faceOpposite_points] at h_mem_face
    rw [fs_def]
    rw [Set.compl_eq_univ_diff] at h_mem_face
    simp
    exact h_mem_face
  rw [h_comb] at h_mem_face'
  have h_i : i ∈ Finset.univ := by simp
  have h_i_notin: i ∉ fs := by grind
  have h1 := s.independent.eq_zero_of_affineCombination_mem_affineSpan hw_P' h_mem_face' h_i h_i_notin
  rw [h_comb] at hx
  rw [Affine.Simplex.affineCombination_mem_interior_iff hw_P] at hx
  have h2 := (hx i).1
  linarith

theorem affineIndependent_of_mem_interior_affineIndependent {a b c p : Pt}
  (h_indep: AffineIndependent ℝ ![a,b,c])
  (hp: p ∈ (⟨_, h_indep⟩: Triangle ℝ Pt).interior) :
  AffineIndependent ℝ ![a,b,p] := by
  sorry

theorem affineIndependent_of_sbtw_affineIndependent {a b c d: Pt}
  (hABC: AffineIndependent ℝ ![a,b,c])
  (hd: Sbtw ℝ a d b) :
  AffineIndependent ℝ ![a, d, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  have h_collinear: Collinear ℝ {a, b, d} := by
    have h:= hd.wbtw.collinear
    apply Collinear.subset _ h
    intro x hx
    simp at hx
    tauto
  have h_indep: AffineIndependent ℝ ![c,a, b] := by simp [hABC]
  have h_ad: a≠ d:= hd.left_ne
  have h:= affineIndependent_of_affineIndependent_collinear h_indep h_collinear h_ad
  have : AffineIndependent ℝ ![a, d, c] := by simp [h]
  rw [←affineIndependent_iff_not_collinear_set]
  exact this

theorem Triangle.mem_interior_of_sbtw_interior {O P: Pt}
  {t : Triangle ℝ Pt}
  (ho: O ∈ t.interior)
  {i : Fin 3}
  (hp : Sbtw ℝ (t.points i) P O) :
  P ∈ t.interior := by
  sorry

theorem Sbtw.dist_lt_of_inner_eq_zero {a b c p: Pt}
    (h_sbtw: Sbtw ℝ a b c)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b < dist p c := by
  obtain ⟨t, ht_mem, hb_eq⟩ := h_sbtw.mem_image_Ioo
  rw [Set.mem_Ioo] at ht_mem
  obtain ⟨ht0, ht1⟩ := ht_mem
  have hb : b -ᵥ a = t • (c -ᵥ a) := by
    rw [← hb_eq, AffineMap.lineMap_apply]
    simp only [vadd_vsub]
  have hpc : ⟪p -ᵥ a, c -ᵥ a⟫ = 0 := by
    have h_eq : ⟪p -ᵥ a, t • (c -ᵥ a)⟫ = 0 := by rwa [←hb]
    rw [inner_smul_right] at h_eq
    have ht_ne_zero : t ≠ 0 := ne_of_gt ht0
    rwa [mul_eq_zero, or_iff_right ht_ne_zero] at h_eq
  have hb_sq : dist p b ^ 2 = dist p a ^ 2 + t^2 * ‖c -ᵥ a‖^2 := by
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    have h_eq : p -ᵥ b = (p -ᵥ a) - (b -ᵥ a) := by simp only [vsub_sub_vsub_cancel_right]
    rw [h_eq, hb, inner_sub_left, inner_sub_right, inner_sub_right]
    rw [inner_smul_right, inner_smul_left, inner_smul_left, inner_smul_right]
    rw [real_inner_comm (p -ᵥ a) (c -ᵥ a), hpc]
    simp
    rw [real_inner_self_eq_norm_sq (c -ᵥ a)]
    ring
  have hc_sq : dist p c ^ 2 = dist p a ^ 2 + ‖c -ᵥ a‖^2 := by
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    have h_eq : p -ᵥ c = (p -ᵥ a) - (c -ᵥ a) := by simp only [vsub_sub_vsub_cancel_right]
    rw [h_eq, inner_sub_left, inner_sub_right, inner_sub_right]
    rw [real_inner_comm (p -ᵥ a) (c -ᵥ a), hpc]
    simp
    rw [real_inner_self_eq_norm_sq (c -ᵥ a)]
  have hpos : 0 < ‖c -ᵥ a‖^2 := by
    have hne : c ≠ a := h_sbtw.left_ne_right.symm
    rw [← real_inner_self_eq_norm_sq]
    rw [real_inner_self_pos]
    rwa [vsub_ne_zero]
  have h_sq_lt : dist p b ^ 2 < dist p c ^ 2 := by
    rw [hb_sq, hc_sq]
    have h_t_sq_lt : t^2 < 1 := by
      rw [sq_lt_one_iff₀ ht0.le]
      exact ht1
    linarith [mul_lt_mul_of_pos_right h_t_sq_lt hpos]
  have h_pos_pb : 0 ≤ dist p b := dist_nonneg
  have h_pos_pc : 0 ≤ dist p c := dist_nonneg
  rwa [← Real.sqrt_lt_sqrt_iff, Real.sqrt_sq h_pos_pb, Real.sqrt_sq h_pos_pc] at h_sq_lt
  exact sq_nonneg (dist p b)

theorem Sbtw.dist_lt_of_angle_eq_pi_div_two {a b c p: Pt}
    (h_sbtw: Sbtw ℝ a b c)
    (h_angle : ∠ b a p = π / 2) :
    dist p b < dist p c := by
  have h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0 := by
    rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    rw [← EuclideanGeometry.angle]
    rw [angle_comm]
    exact h_angle
  exact Sbtw.dist_lt_of_inner_eq_zero h_sbtw h_inner

theorem sbtw_expand {a b c d : Pt}
    (h₁ : Sbtw ℝ a b c) (h₂ : Sbtw ℝ b c d) :
    Sbtw ℝ a b d := by
  rw[← angle_eq_pi_iff_sbtw]
  rw[← angle_eq_pi_iff_sbtw] at h₁
  have h_angle : ∠ a b c = ∠ a b d := by
    apply angle_eq_of_sbtw
    exact h₂
  rw[← h_angle]
  exact h₁

theorem collinear_insert_insert_of_collinear_collinear_ne {p₁ p₂ p₃ p₄ : Pt}
  (h1 : Collinear ℝ {p₁, p₃, p₄}) (h2 : Collinear ℝ {p₂, p₃, p₄}) (h_ne : p₃ ≠ p₄):
  Collinear ℝ {p₁, p₂, p₃, p₄} := by
  have h1: p₁ ∈ affineSpan ℝ {p₃, p₄} := by
    apply Collinear.mem_affineSpan_of_mem_of_ne h1
    repeat aesop
  have h2: p₂ ∈ affineSpan ℝ {p₃, p₄} := by
    apply Collinear.mem_affineSpan_of_mem_of_ne h2
    repeat aesop
  exact collinear_insert_insert_of_mem_affineSpan_pair h1 h2

namespace EuclideanGeometry.Sphere

lemma IsTangentAt.dist_eq_of_tangentFrom {s : Sphere Pt} {p₁ p₂ q : Pt} {as₁ as₂ : AffineSubspace ℝ Pt}
    (h₁ : s.IsTangentAt p₁ as₁) (h₂ : s.IsTangentAt p₂ as₂) (hq_mem₁ : q ∈ as₁) (hq_mem₂ : q ∈ as₂) :
    dist q p₁ = dist q p₂ := by
  have h1 := EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem h₁ hq_mem₁
  have h2 := EuclideanGeometry.Sphere.IsTangentAt.dist_sq_eq_of_mem h₂ hq_mem₂
  rw [h1] at h2
  rw [add_left_cancel_iff] at h2
  simp at h2
  exact h2

lemma IsTangentAt.angle_eq_pi_div_two {s : Sphere Pt} {p q : Pt} {as : AffineSubspace ℝ Pt}
    (h : s.IsTangentAt p as)  (hq_mem : q ∈ as):
    ∠ q p s.center = π / 2 := by
  have h1 := EuclideanGeometry.Sphere.IsTangentAt.inner_left_eq_zero_of_mem h hq_mem
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two] at h1
  rw [EuclideanGeometry.angle, ←neg_vsub_eq_vsub_rev _ s.center, InnerProductGeometry.angle_neg_right, h1]
  linarith

lemma IsTangentAt_of_angle_eq_pi_div_two {s : Sphere Pt} {p q : Pt}
    (h : ∠ q p s.center = π / 2) (hp : p ∈ s) :
    s.IsTangentAt p line[ℝ, p ,q] := by
    have hp_mem : p ∈ line[ℝ, p, q] :=left_mem_affineSpan_pair ℝ p q
    refine ⟨hp,hp_mem,?_⟩
    have h_ortho : ⟪q -ᵥ p, p -ᵥ  s.center⟫ = 0 := by
      rw [EuclideanGeometry.angle] at h
      rw [←InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two] at h
      rw [←neg_vsub_eq_vsub_rev p s.center, inner_neg_right, neg_eq_zero] at h
      exact h
    have hq : q ∈ s.orthRadius p := by
      simp [Sphere.mem_orthRadius_iff_inner_left, h_ortho]
    rw [affineSpan_le]
    have hp: p ∈ s.orthRadius p := by
      simp [EuclideanGeometry.Sphere.self_mem_orthRadius]
    simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hp, hq⟩

end EuclideanGeometry.Sphere

namespace EuclideanGeometry

theorem Sbtw.dist_lt_dist_perpbisector {a b c p : Pt}
    (h_sbtw: Sbtw ℝ a b c)
    (hp: p ∈ AffineSubspace.perpBisector a b) :
    dist p b < dist p c := by
    set o := midpoint ℝ a b with o_def
    have ho : Sbtw ℝ a o b := by
      rw [o_def]
      apply sbtw_midpoint_of_ne
      exact h_sbtw.left_ne
    have h_sbtw' : Sbtw ℝ o b c := by
      exact Sbtw.trans_left_right h_sbtw ho
    have h_inner : ⟪p -ᵥ o, b -ᵥ o⟫ = 0 := by
      rw [o_def]
      have h_perp := AffineSubspace.mem_perpBisector_iff_inner_eq_zero.mp hp
      have h_scale : b -ᵥ midpoint ℝ a b = (1/2 : ℝ) • (b -ᵥ a) := by
        simp only [right_vsub_midpoint, invOf_eq_inv, one_div]
      rw [h_scale]
      rw [inner_smul_right, h_perp, mul_zero]
    apply Sbtw.dist_lt_of_inner_eq_zero h_sbtw' h_inner

end EuclideanGeometry

namespace EuclideanGeometry.Sphere

lemma IsTangenAt_iff_angle_eq_pi_div_two {s : Sphere Pt} {p q : Pt} (hp : p ∈ s) :
    s.IsTangentAt p line[ℝ, p ,q] ↔ ∠ q p s.center = π / 2 := by
  constructor
  · intro h
    apply IsTangentAt.angle_eq_pi_div_two h
    exact right_mem_affineSpan_pair ℝ p q
  · intro h
    exact IsTangentAt_of_angle_eq_pi_div_two h hp

theorem is_tangentAt_of_dist_sq_eq_power {t p : Pt} {s : Sphere Pt} (ht : t ∈ s)
    (h_dist_eq : dist p t ^ 2 = s.power p) :
    s.IsTangentAt t (line[ℝ, p, t]) := by
  have : affineSpan ℝ {p, t} = affineSpan ℝ {t, p} := by
    rw [Set.pair_comm]
  rw [this, IsTangenAt_iff_angle_eq_pi_div_two ht]
  have h_pythag : dist p t ^ 2 + dist t s.center ^ 2 = dist p s.center ^ 2 := by
    rw [h_dist_eq, EuclideanGeometry.Sphere.power, mem_sphere.mp ht]
    ring
  have h := dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p t s.center
  rw [sq, sq, sq] at h_pythag
  rw [dist_comm t s.center] at h_pythag
  exact h.mp h_pythag.symm

end EuclideanGeometry.Sphere

section
open scoped EuclideanGeometry Real
open EuclideanGeometry

end

end lemmas



variable (cfg : Imo2012Q5Cfg V Pt)

open scoped Affine EuclideanGeometry Real




theorem not_col_ABC : ¬Collinear ℝ {cfg.A, cfg.B, cfg.C} :=
  affineIndependent_iff_not_collinear_set.mp cfg.affine_indep_ABC


theorem h_A : cfg.triangle_ABC.points 0 = cfg.A := by sorry
theorem h_B : cfg.triangle_ABC.points 1 = cfg.B := by sorry
theorem h_C : cfg.triangle_ABC.points 2 = cfg.C := by sorry

theorem X_mem_CD : cfg.X ∈ line[ℝ, cfg.C, cfg.D] := cfg.Sbtw_CXD.wbtw.mem_affineSpan

def sphere_A := EuclideanGeometry.Sphere.mk cfg.A (dist cfg.A cfg.C)
def sphere_B := EuclideanGeometry.Sphere.mk cfg.B (dist cfg.B cfg.C)

theorem sphere_a : cfg.sphere_A = EuclideanGeometry.Sphere.mk cfg.A (dist cfg.A cfg.C) := by rfl
theorem sphere_b : cfg.sphere_B = EuclideanGeometry.Sphere.mk cfg.B (dist cfg.B cfg.C) := by rfl


theorem C_mem_sphere_A : cfg.C ∈ cfg.sphere_A := by
  apply mem_sphere.mpr
  rw [EuclideanGeometry.Sphere.radius, dist_comm]
  rfl

theorem C_mem_sphere_B : cfg.C ∈ cfg.sphere_B := by
  apply mem_sphere.mpr
  rw [EuclideanGeometry.Sphere.radius, dist_comm]
  rfl

theorem dist_CA_eq_radius_A : dist cfg.C cfg.A = cfg.sphere_A.radius := by
  rw [EuclideanGeometry.Sphere.radius, dist_comm]
  rfl


theorem dist_CB_eq_radius_B : dist cfg.C cfg.B = cfg.sphere_B.radius := by
  rw [EuclideanGeometry.Sphere.radius, dist_comm]
  rfl

def v_XK := cfg.X -ᵥ cfg.K
def v_XL := cfg.X -ᵥ cfg.L


theorem K_mem_sphere_B : cfg.K ∈ cfg.sphere_B := by
  apply mem_sphere.mpr
  rw [← dist_CB_eq_radius_B, dist_comm cfg.C]
  rw [← BK_eq_BC]
  rw [dist_comm cfg.B cfg.K]
  rfl

theorem L_mem_sphere_A : cfg.L ∈ cfg.sphere_A := by
  apply mem_sphere.mpr
  rw [← dist_CA_eq_radius_A, dist_comm cfg.C]
  rw [← AL_eq_AC]
  rw [dist_comm cfg.A cfg.L]
  rfl

def K' := cfg.sphere_B.secondInter cfg.K cfg.v_XK
def L' := cfg.sphere_A.secondInter cfg.L cfg.v_XL


theorem h_sphere_A_radius : 0 ≤ cfg.sphere_A.radius := Sphere.radius_nonneg_of_mem
    cfg.C_mem_sphere_A
theorem h_sphere_B_radius : 0 ≤ cfg.sphere_B.radius := Sphere.radius_nonneg_of_mem
    cfg.C_mem_sphere_B

theorem h_angle_CDB : ∠ cfg.C cfg.D cfg.B = π / 2 := by
  rw [cfg.D_eq_altitudeFoot]
  have h_ne: (2: Fin 3) ≠ 1 := by simp
  -- have := angle_point_altitudeFoot_eq_pi_div_two cfg.triangle_ABC h_ne
  -- rw [h_C, h_B] at this
  -- exact this
  sorry

theorem h_angle_CDA : ∠ cfg.C cfg.D cfg.A = π / 2 := by
  rw [cfg.D_eq_altitudeFoot]
  have h_ne: (2: Fin 3) ≠ 0 := by simp
  -- have := angle_point_altitudeFoot_eq_pi_div_two cfg.triangle_ABC h_ne
  -- rw [h_C, h_A] at this
  -- exact this
  sorry

theorem h_BDX_eq_BDC : ∠ cfg.B cfg.D cfg.X = ∠ cfg.B cfg.D cfg.C := by
  apply angle_eq_of_sbtw
  exact cfg.Sbtw_CXD.symm

theorem h_ADX_eq_ADC : ∠ cfg.A cfg.D cfg.X = ∠ cfg.A cfg.D cfg.C := by
  apply angle_eq_of_sbtw
  exact cfg.Sbtw_CXD.symm

theorem dist_X_sphere_B : dist cfg.X cfg.sphere_B.center < cfg.sphere_B.radius := by
  rw [dist_comm]
  have : cfg.sphere_B.radius = dist cfg.B cfg.C := by rfl
  simp_rw [this, cfg.sphere_b]
  apply Sbtw.dist_lt_of_angle_eq_pi_div_two cfg.Sbtw_CXD.symm
  rw [angle_comm, h_BDX_eq_BDC, angle_comm, h_angle_CDB]

theorem dist_X_sphere_A : dist cfg.X cfg.sphere_A.center < cfg.sphere_A.radius := by
  rw [dist_comm]
  have : cfg.sphere_A.radius = dist cfg.A cfg.C := by simp [sphere_a]
  rw [this, sphere_a]
  apply Sbtw.dist_lt_of_angle_eq_pi_div_two cfg.Sbtw_CXD.symm
  rw [angle_comm, h_ADX_eq_ADC, angle_comm, h_angle_CDA]

theorem hKXK' : Sbtw ℝ cfg.K cfg.X cfg.K' := by
  have := Sphere.sbtw_secondInter cfg.K_mem_sphere_B cfg.dist_X_sphere_B
  exact this

theorem hLXL' : Sbtw ℝ cfg.L cfg.X cfg.L' := by
  have := Sphere.sbtw_secondInter cfg.L_mem_sphere_A cfg.dist_X_sphere_A
  exact this

theorem pow_X_eq : cfg.sphere_A.power cfg.X = cfg.sphere_B.power cfg.X := by
  unfold Sphere.power
  have h1:= EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two cfg.A cfg.D
    cfg.X
  have angle_ADX : ∠ cfg.A cfg.D cfg.X = π / 2 := by rw [h_ADX_eq_ADC, angle_comm, h_angle_CDA]
  have dist_sq_A := h1.mpr angle_ADX

  have h2:= EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two cfg.B cfg.D
    cfg.X
  have angle_BDX : ∠ cfg.B cfg.D cfg.X = π / 2 := by rw [h_BDX_eq_BDC, angle_comm, h_angle_CDB]
  have dist_sq_B := h2.mpr angle_BDX

  simp_rw [← pow_two] at dist_sq_A dist_sq_B
  simp [cfg.sphere_a, cfg.sphere_b]
  rw [dist_comm cfg.X cfg.A, dist_comm cfg.X cfg.B]
  rw [dist_sq_A, dist_sq_B]

  have h3:= EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two cfg.A cfg.D
    cfg.C
  have angle_ADC : ∠ cfg.A cfg.D cfg.C = π / 2 := by rw [angle_comm, h_angle_CDA]
  have dist_sq_AC := h3.mpr angle_ADC
  simp_rw [← pow_two] at dist_sq_AC

  have h4:= EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two cfg.B cfg.D
    cfg.C
  have angle_BDC : ∠ cfg.B cfg.D cfg.C = π / 2 := by rw [angle_comm, h_angle_CDB]
  have dist_sq_BC := h4.mpr angle_BDC
  simp_rw [← pow_two] at dist_sq_BC

  rw [dist_sq_AC, dist_sq_BC]
  ring

theorem h_L_A : cfg.L ∈ cfg.sphere_A := cfg.L_mem_sphere_A
theorem h_K_B : cfg.K ∈ cfg.sphere_B := cfg.K_mem_sphere_B
theorem h_L'_A : cfg.L' ∈ cfg.sphere_A := by unfold Imo2012Q5Cfg.L'; simp; exact cfg.h_L_A
theorem h_K'_B : cfg.K' ∈ cfg.sphere_B := by unfold Imo2012Q5Cfg.K'; simp; exact cfg.h_K_B

theorem pow_X_B : -cfg.sphere_B.power cfg.X = dist cfg.X cfg.K * dist cfg.X cfg.K' := by
  rw [Sphere.mul_dist_eq_neg_power_of_dist_center_le_radius cfg.h_sphere_B_radius cfg.hKXK'.wbtw.mem_affineSpan
    cfg.h_K_B cfg.h_K'_B]
  have angle_XDB: ∠ cfg.X cfg.D cfg.B = π / 2 := by
    rw [angle_comm, angle_eq_of_sbtw cfg.Sbtw_CXD.symm, angle_comm]
    exact cfg.h_angle_CDB
  have dist_lt := Sbtw.dist_lt_of_angle_eq_pi_div_two cfg.Sbtw_CXD.symm angle_XDB
  rw [dist_comm cfg.B cfg.X] at dist_lt
  simp_rw [sphere_b]
  grind

theorem pow_X_A : -cfg.sphere_A.power cfg.X = dist cfg.X cfg.L * dist cfg.X cfg.L' := by
  rw [Sphere.mul_dist_eq_neg_power_of_dist_center_le_radius cfg.h_sphere_A_radius cfg.hLXL'.wbtw.mem_affineSpan
    cfg.h_L_A cfg.h_L'_A]
  have angle_XDA: ∠ cfg.X cfg.D cfg.A = π / 2 := by
    rw [angle_comm, angle_eq_of_sbtw cfg.Sbtw_CXD.symm, angle_comm]
    exact cfg.h_angle_CDA
  have dist_lt:= Sbtw.dist_lt_of_angle_eq_pi_div_two cfg.Sbtw_CXD.symm angle_XDA
  rw [dist_comm cfg.A cfg.X] at dist_lt
  simp_rw [sphere_a]
  grind

theorem hx : dist cfg.X cfg.K * dist cfg.X cfg.K' = dist cfg.X cfg.L * dist cfg.X cfg.L' := by
  rw [← pow_X_A, ← pow_X_B, pow_X_eq]

theorem X_mem_interior : cfg.X ∈ cfg.triangle_ABC.interior := by
  have sbtw_ADB : Sbtw ℝ cfg.A cfg.D cfg.B := by
    rw [cfg.D_eq_altitudeFoot]
    rw [← h_A, ←h_B]
    apply sbtw_altitudeFoot_of_rightAngled (by simp) (by simp) (by simp)
    rw [h_A, h_B, h_C, angle_comm]
    exact cfg.angle_BCA
  have hne1 : (2: Fin 3) ≠ 0 := by simp
  have hne2 : (0: Fin 3) ≠ 1 := by simp
  have hne3 : (1: Fin 3) ≠ 2 := by simp
  have sbtw_ADB' := sbtw_ADB
  rw [←h_B, ←h_A] at sbtw_ADB'
  have sbtw_CXD' := cfg.Sbtw_CXD
  rw [←h_C] at sbtw_CXD'
  exact Triangle.mem_interior_of_sbtw_sbtw cfg.triangle_ABC hne1 hne2 hne3 sbtw_ADB' sbtw_CXD'

theorem indep_ABX : AffineIndependent ℝ ![cfg.A, cfg.B, cfg.X] := by
  apply affineIndependent_of_mem_interior_affineIndependent cfg.affine_indep_ABC
  exact cfg.X_mem_interior V Pt


theorem notcol_KXL : ¬ Collinear ℝ {cfg.K, cfg.X, cfg.L} := by
  rw [← affineIndependent_iff_not_collinear_set]
  have indep_XAB: AffineIndependent ℝ ![cfg.X, cfg.A, cfg.B] := by simp [indep_ABX]
  have h1:= affineIndependent_of_sbtw_affineIndependent indep_XAB cfg.Sbtw_AKX.symm
  have indep_XBK : AffineIndependent ℝ ![cfg.X, cfg.B, cfg.K] := by simp [h1]
  have h2 := affineIndependent_of_sbtw_affineIndependent indep_XBK cfg.Sbtw_BLX.symm
  simp [h2]

theorem cosphereic_set_ω : Cospherical {cfg.K, cfg.K', cfg.L, cfg.L'} := by
  apply cospherical_of_mul_dist_eq_mul_dist notcol_KXL hKXK' hLXL'
  simp [hx, dist_comm]

theorem sphere_ω : EuclideanGeometry.Sphere Pt := (cospherical_iff_exists_sphere.mp cosphereic_set_ω).choose

theorem h_ω : ∀ p ∈ {cfg.K, cfg.K', cfg.L, cfg.L'}, p ∈ sphere_ω := (cospherical_iff_exists_sphere.mp cosphereic_set_ω).choose_spec

theorem h_L : cfg.L ∈ sphere_ω := h_ω cfg.L (by simp)
theorem h_K : cfg.K ∈ sphere_ω := h_ω cfg.K (by simp)
theorem h_L' : cfg.L' ∈ sphere_ω := h_ω cfg.L' (by simp)
theorem h_K' : cfg.K' ∈ sphere_ω := h_ω cfg.K' (by simp)

theorem h_sphere_ω_radius_nonneg : 0 ≤ sphere_ω.radius := Sphere.radius_nonneg_of_mem h_L

theorem L_ne_L' : cfg.L ≠ cfg.L' := hLXL'.left_ne_right
theorem K_ne_K' : cfg.K ≠ cfg.K' := hKXK'.left_ne_right

theorem h_L_interior : cfg.L ∈ cfg.triangle_ABC.interior := by
  have := cfg.Sbtw_BLX
  rw [← h_B] at this
  exact Triangle.mem_interior_of_sbtw_interior X_mem_interior this

theorem h_K_interior : cfg.K ∈ cfg.triangle_ABC.interior := by
  have := cfg.Sbtw_AKX
  rw [← h_A] at this
  exact Triangle.mem_interior_of_sbtw_interior X_mem_interior this

theorem sbtw_L'LB : Sbtw ℝ cfg.L' cfg.L cfg.B := by
  rw [sbtw_comm]
  exact sbtw_expand cfg.Sbtw_BLX hLXL'

theorem sbtw_K'KA : Sbtw ℝ cfg.K' cfg.K cfg.A := by
  rw [sbtw_comm]
  exact sbtw_expand cfg.Sbtw_AKX hKXK'

theorem h_B_L_L' : cfg.B ∈ affineSpan ℝ {cfg.L, cfg.L'} := by
  have h1 := Sphere.secondInter_collinear cfg.sphere_A cfg.L cfg.X
  have h2:= cfg.Sbtw_BLX.wbtw.collinear
  have h3: Collinear ℝ {cfg.B, cfg.L', cfg.L, cfg.X} := by
    apply collinear_insert_insert_of_collinear_collinear_ne h2 ?_ cfg.Sbtw_BLX.ne_right
    rw [Set.insert_comm]
    rw [Set.pair_comm]
    exact h1
  apply h3.mem_affineSpan_of_mem_of_ne
  repeat simp
  exact L_ne_L'

theorem h_A_K_K' : cfg.A ∈ affineSpan ℝ {cfg.K, cfg.K'} := by
  have h := Sphere.secondInter_collinear cfg.sphere_B cfg.K cfg.X
  have h2:= cfg.Sbtw_AKX.wbtw.collinear
  have h3: Collinear ℝ {cfg.A, cfg.K', cfg.K, cfg.X} := by
    apply collinear_insert_insert_of_collinear_collinear_ne h2 ?_ cfg.Sbtw_AKX.ne_right
    rw [Set.insert_comm]
    rw [Set.pair_comm]
    exact h
  apply h3.mem_affineSpan_of_mem_of_ne
  repeat simp
  exact K_ne_K'

theorem power_B_A : (dist cfg.B cfg.C) ^ 2 = dist cfg.B cfg.L * dist cfg.B cfg.L' := by
  apply EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant h_L_A h_L'_A h_B_L_L'
  rw [Set.pair_comm]
  apply EuclideanGeometry.Sphere.IsTangentAt_of_angle_eq_pi_div_two ?_ h_C_in_A
  rw [sphere_a]
  exact cfg.angle_BCA

theorem power_A_B : (dist cfg.A cfg.C) ^ 2 = dist cfg.A cfg.K * dist cfg.A cfg.K' := by
  apply EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant h_K_B h_K'_B h_A_K_K'
  rw [Set.pair_comm]
  apply EuclideanGeometry.Sphere.IsTangentAt_of_angle_eq_pi_div_two ?_ h_C_in_B
  rw [sphere_b]
  rw [angle_comm] at cfg.angle_BCA
  exact cfg.angle_BCA

theorem h_power_ω_B : sphere_ω.power cfg.B = dist cfg.B cfg.L * dist cfg.B cfg.L' := by
  rw [Sphere.mul_dist_eq_power_of_radius_le_dist_center h_sphere_ω_radius_nonneg h_B_L_L' h_L h_L']
  have h1: sphere_ω.center ∈ AffineSubspace.perpBisector cfg.L' cfg.L := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    rw [dist_comm _ cfg.L, dist_comm _ cfg.L']
    exact dist_center_eq_dist_center_of_mem_sphere h_L' h_L
  have := EuclideanGeometry.Sbtw.dist_lt_dist_perpbisector sbtw_L'LB h1
  have h2: dist sphere_ω.center cfg.L = sphere_ω.radius := by
    rw [dist_comm]
    exact mem_sphere.mp h_L
  rw [h2, dist_comm] at this
  exact le_of_lt this

theorem h_power_ω_A : sphere_ω.power cfg.A = dist cfg.A cfg.K * dist cfg.A cfg.K' := by
  rw [Sphere.mul_dist_eq_power_of_radius_le_dist_center h_sphere_ω_radius_nonneg h_A_K_K' h_K h_K']
  have h1: sphere_ω.center ∈ AffineSubspace.perpBisector cfg.K' cfg.K := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    rw [dist_comm _ cfg.K, dist_comm _ cfg.K']
    exact dist_center_eq_dist_center_of_mem_sphere h_K' h_K
  have := EuclideanGeometry.Sbtw.dist_lt_dist_perpbisector sbtw_K'KA h1
  have h2: dist sphere_ω.center cfg.K = sphere_ω.radius := by
    rw [dist_comm]
    exact mem_sphere.mp h_K
  rw [h2, dist_comm] at this
  exact le_of_lt this

theorem h_tangent_at_K_ω : sphere_ω.IsTangentAt cfg.K (line[ℝ, cfg.B, cfg.K]) := by
  apply EuclideanGeometry.Sphere.is_tangentAt_of_dist_sq_eq_power h_K
  rw [h_power_ω_B]
  exact power_B_A

theorem h_tangent_at_L_ω : sphere_ω.IsTangentAt cfg.L (line[ℝ, cfg.A, cfg.L]) := by
  apply EuclideanGeometry.Sphere.is_tangentAt_of_dist_sq_eq_power h_L
  rw [h_power_ω_A]
  exact power_A_B

end Imo2012Q5Cfg



end

end Imo2012Q5


open Imo2012Q5

theorem imo2012_q5 {A B C D X K L M : Pt}
    (affine_indep_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (h_triange_eq : triangle_ABC = ⟨![A, B, C], affine_indep_ABC⟩)
    (angle_BCA : ∠ B C A = π / 2)
    (D_eq_altitudeFoot : D = triangle_ABC.altitudeFoot 2)
    (Sbtw_CXD : Sbtw ℝ C X D)
    (Sbtw_AKX : Sbtw ℝ A K X)
    (BK_eq_BC : dist B K = dist B C)
    (Sbtw_BLX : Sbtw ℝ B L X)
    (AL_eq_AC : dist A L = dist A C)
    (M_mem_inf_AL_BK : M ∈ line[ℝ, A, L] ⊓ line[ℝ, B, K]) :
    dist M K = dist M L := by
  let cfg : Imo2012Q5Cfg V Pt := {
    A, B, C, D, X, K, L, M,
    affine_indep_ABC,
    triangle_ABC,
    angle_BCA,
    D_eq_altitudeFoot,
    Sbtw_CXD,
    Sbtw_AKX,
    BK_eq_BC,
    Sbtw_BLX,
    AL_eq_AC,
    M_mem_inf_AL_BK
  }
  exact EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_tangentFrom
    (Imo2012Q5Cfg.h_tangent_at_K_ω cfg) (Imo2012Q5Cfg.h_tangent_at_L_ω cfg) cfg.M_mem_inf_AL_BK.2 cfg.M_mem_inf_AL_BK.1
