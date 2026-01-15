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
import Mathlib.LinearAlgebra.AffineSpace.Ordered

import Mathlib.Tactic
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

open Affine Affine.Simplex EuclideanGeometry Module

open scoped Affine EuclideanGeometry Real


attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]


namespace Lemma

set_option linter.flexible false in

noncomputable section



-- Lemmas from test.lean

open RealInnerProductSpace


open EuclideanGeometry Real
open Affine Module
open scoped EuclideanGeometry
open scoped RealInnerProductSpace

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]


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

open scoped Finset

theorem Simplex.notMem_affineSpan_face_of_exist_of_mem_interior {n m : ℕ} [NeZero n] (s: Simplex ℝ Pt n)
    {x : Pt} (hx : x ∈ s.interior)
    {f : Finset (Fin (n + 1))} (fs : #f = m+1) (hi : ∃ i, i ∉ f) :
    x ∉ affineSpan ℝ (Set.range (s.face fs).points) := by
  have h_mem : x ∈ affineSpan ℝ (Set.range s.points) := by
    have hx1:= hx
    rcases hx1 with ⟨w, hw, ⟨_, hx2⟩⟩
    rw [← hx2]
    apply affineCombination_mem_affineSpan hw
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype h_mem with ⟨w, hw, h_comb⟩
  rw [h_comb] at hx
  rw [Affine.Simplex.affineCombination_mem_interior_iff hw] at hx

  obtain ⟨i, hi_notin⟩ := hi
  have hi1 := hx i
  have h1 : x ∉ (s.face fs).interior :=by
    rw [h_comb]
    intro h_mem_face
    have : NeZero m := by sorry
    rw [Affine.Simplex.affineCombination_mem_interior_face_iff_pos _ _ hw] at h_mem_face
    obtain ⟨_, hi3⟩ := h_mem_face
    have := hi3 i hi_notin
    grind

  suffices hi' : ∃ i ∉ f, w i ≠ 0 by
    sorry

  have h2 := (s.affineCombination_mem_closedInterior_face_iff_nonneg fs hw).mp

theorem Simplex.notMem_affineSpan_faceOpposite_of_mem_interior {n:ℕ} [NeZero n] (s: Simplex ℝ Pt n)
    (i : Fin (n + 1)) {x : Pt} (hx : x ∈ s.interior) :
  x ∉ affineSpan ℝ (Set.range (s.faceOpposite i).points) := by
  have zoer_lt: 0 < n := by grind [NeZero.ne n]
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

theorem affineIndependent_of_mem_interior_affineIndependent' {a b c p : Pt}
  (h_indep: AffineIndependent ℝ ![a,b,c])
  (hp: p ∈ (⟨_, h_indep⟩: Triangle ℝ Pt).interior) :
  AffineIndependent ℝ ![a,b,p] := by

  have hp_notMem : p ∉ affineSpan ℝ {a , b} := by
    sorry

  have hne : a ≠ b := ne₁₂_of_not_collinear (by
    rw [affineIndependent_iff_not_collinear_set] at h_indep
    exact h_indep)
  have ha : a ∈ line[ℝ, a, b] := by grind [left_mem_affineSpan_pair]
  have hb : b ∈ line[ℝ, a, b] := by grind [right_mem_affineSpan_pair]
  apply affineIndependent_of_ne_of_mem_of_mem_of_notMem hne ha hb hp_notMem

theorem affineIndependent_of_mem_interior_affineIndependent {a b c p : Pt}
  (h_indep: AffineIndependent ℝ ![a,b,c])
  (hp: p ∈ (⟨_, h_indep⟩: Triangle ℝ Pt).interior) :
  AffineIndependent ℝ ![a,b,p] := by
  set t := (⟨_, h_indep⟩: Triangle ℝ Pt) with t_def
  have notcol_abc: ¬ Collinear ℝ {a, b, c} := by
    rw [affineIndependent_iff_not_collinear_set] at h_indep
    exact h_indep
  have hp_mem: p ∈ affineSpan ℝ (Set.range t.points) := by
    have hp1:= hp
    rcases hp1 with ⟨w, hw, ⟨_, hp2⟩⟩
    rw [← hp2]
    apply affineCombination_mem_affineSpan hw
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype hp_mem with ⟨w_P, hw_P, hsum_P⟩
  have hp_interior:= hp
  rw [hsum_P] at hp
  rw [Affine.Simplex.affineCombination_mem_interior_iff hw_P] at hp
  have hp_not_mem : p ∉ affineSpan ℝ {a , b} := by
    have h1:= Simplex.notMem_affineSpan_faceOpposite_of_mem_interior t 2 hp_interior
    rw [Simplex.range_faceOpposite_points] at h1
    simp at h1
    have h2: t.points '' {2}ᶜ = {a, b} := by
      have h3: {2}ᶜ = ({0, 1} : Set (Fin 3)) := by
        rw [Set.compl_eq_univ_diff]
        grind
      rw [h3]
      simp [t_def]
      aesop
    rw [h2] at h1
    exact h1
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have a_ne_b : a ≠ b := ne₁₂_of_not_collinear notcol_abc
  have hp_mem : p ∈  ({a, b, p} : Set Pt) := by aesop
  have h2:= h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) hp_mem a_ne_b
  aesop

theorem affineIndependent_of_sbtw_affineIndependent'' {a b c d: Pt}
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

variable [AddCommMonoid Pt] [SMul ℝ Pt]

namespace EuclideanGeometry.Sphere


end EuclideanGeometry.Sphere


section
open scoped EuclideanGeometry Real
open EuclideanGeometry


end

end

end Lemma
