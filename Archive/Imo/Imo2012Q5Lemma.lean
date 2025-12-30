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
import Mathlib.Geometry.Euclidean.Similarity

import Mathlib.Tactic


open Affine Affine.Simplex EuclideanGeometry Module

open scoped Affine EuclideanGeometry Real


attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]



noncomputable section

-- Lemmas from test.lean

open RealInnerProductSpace


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
    (h_indep : AffineIndependent k p)
    {q₁ q₂ q₃ : P}
    {w₁ w₂ w₃ : ι → k}
    (hq₁ : q₁ = affineCombination k univ p w₁)
    (hq₂ : q₂ = affineCombination k univ p w₂)
    (hq₃ : q₃ = affineCombination k univ p w₃)
    (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1) (hw₃ : ∑ i, w₃ i = 1)
    {c : k}
    (hline : q₂ = (AffineMap.lineMap q₁ q₃) c) :
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

theorem AffineSubspace.Sbtw.oangle_sign_eq_of_sbtw_sbtw
    [Fact (finrank ℝ V = 2)]
    [ho : Oriented ℝ V (Fin 2)]
    {p p₁ p₂ p₃ p₄ : Pt}
    (hp₁₃ : Sbtw ℝ p₁ p p₃) (hp₂₄ : Sbtw ℝ p₂ p p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  rw [← Sbtw.oangle_eq_right hp₂₄.symm, Sbtw.oangle_sign_eq _ hp₁₃, ← oangle_rotate_sign,
    Sbtw.oangle_sign_eq _ hp₂₄.symm, Sbtw.oangle_eq_left hp₁₃.symm]

theorem AffineSubspace.Sbtw.oangle_sign_eq_of_sbtw_sbtw'
    [Fact (finrank ℝ V = 2)]
    [ho : Oriented ℝ V (Fin 2)]
    {p p₁ p₂ p₃ p₄ : Pt}
    (hp₁₃ : Sbtw ℝ p p₁ p₃) (hp₂₄ : Sbtw ℝ p p₂ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  rw [Sbtw.oangle_eq_right hp₂₄.symm, Sbtw.oangle_sign_eq_right _ hp₁₃.symm, oangle_rotate_sign,
    ← Sbtw.oangle_sign_eq_left p₃ hp₂₄, Sbtw.oangle_eq_left hp₁₃.symm]

theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi [Fact (Module.finrank ℝ V = 2)]
    [Module.Oriented ℝ V (Fin 2)] {a b c d p : Pt} (h : dist a p * dist b p = dist c p * dist d p)
    (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) (hn : ¬ Collinear ℝ ({a, p, c} : Set Pt)) :
    Cospherical ({a, b, c, d} : Set Pt) := by
  suffices h_equiv : Cospherical ({a, b, d, c} : Set Pt) by
    grind [Set.pair_comm d c]
  have h_angle_eq : ∠ a p d = ∠ c p b := by
    grind [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hcpd]
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hapb hcpd
  have h_notcol_abc : ¬ Collinear ℝ ({a, b, c} : Set Pt) := by
    intro hcol
    have hcol_apb := hapb.wbtw.collinear
    suffices hcol : Collinear ℝ ({a, p, c} : Set Pt) by grind
    suffices hcol_apcb : Collinear ℝ ({c, p, a, b} : Set Pt) by grind [Collinear.subset _ hcol_apcb]
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hapb.left_ne_right]
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hapb.left_ne_right]
  apply EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear ?_ h_notcol_abc
  suffices h2 : ∡ a b c = ∡ a d c by grind
  suffices h3 : ∠ a b c = ∠ a d c by
    grind [oangle_eq_of_angle_eq_of_sign_eq, AffineSubspace.Sbtw.oangle_sign_eq_of_sbtw_sbtw]
  rw [angle_comm, ← angle_eq_of_sbtw hapb.symm]
  symm
  rw [← angle_eq_of_sbtw hcpd.symm]
  suffices h_sim : Similar ![a, p, d] ![c, p, b] by
    grind [angle_comm, h_sim.angle_eq_all.right.left]
  have h_notcol_apd : ¬ Collinear ℝ ({a, p, d} : Set Pt) := by
    intro hcol
    have hcol_cpd := hcpd.wbtw.collinear
    suffices hcol : Collinear ℝ ({a, c, p, d} : Set Pt) by
      have : Collinear ℝ ({a, p, c} : Set Pt) := by grind [Collinear.subset _ hcol]
      exact hn this
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hcpd.ne_right]
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hcpd.ne_right]
  have h_notcol_cpb : ¬ Collinear ℝ ({c, p, b} : Set Pt) := by
    intro hcol
    have hcol_apb := hapb.wbtw.collinear
    suffices hcol : Collinear ℝ ({c, a, p, b} : Set Pt) by
      have : Collinear ℝ ({a, p, c} : Set Pt) := by grind [Collinear.subset _ hcol]
      exact hn this
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hapb.ne_right]
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hapb.ne_right]
  apply similar_of_side_angle_side h_notcol_apd h_notcol_cpb h_angle_eq ?_
  grind [dist_comm]

theorem angle_point_altitudeFoot_eq_pi_div_two (t : Affine.Triangle ℝ Pt)
    {i j : Fin 3} (h : i ≠ j) :
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


namespace EuclideanGeometry.Sphere


end EuclideanGeometry.Sphere


section
open scoped EuclideanGeometry Real
open EuclideanGeometry

end
