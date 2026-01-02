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

import Archive.Imo.Imo2012Q5Lemma

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
  triangle_ABC : Triangle ℝ Pt
  triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affine_indep_ABC⟩
  angle_BCA : ∠ B C A = π / 2
  D_eq_altitudeFoot : D = triangle_ABC.altitudeFoot 2
  Sbtw_CXD : Sbtw ℝ C X D
  Sbtw_AKX : Sbtw ℝ A K X
  BK_eq_BC : dist B K = dist B C
  Sbtw_BLX : Sbtw ℝ B L X
  AL_eq_AC : dist A L = dist A C
  M_mem_inf_AL_BK : M ∈ line[ℝ, A, L] ⊓ line[ℝ, B, K]

namespace Imo2012Q5Cfg

variable {cfg : Imo2012Q5Cfg V Pt}

def symm : Imo2012Q5Cfg V Pt where
  A := cfg.B
  B := cfg.A
  C := cfg.C
  D := cfg.D
  X := cfg.X
  K := cfg.L
  L := cfg.K
  M := cfg.M
  affine_indep_ABC := cfg.affine_indep_ABC.comm_left
  triangle_ABC := ⟨![cfg.B, cfg.A, cfg.C], cfg.affine_indep_ABC.comm_left⟩
  triangle_ABC_def := by rfl
  angle_BCA := by
    rw [angle_comm]
    exact cfg.angle_BCA
  D_eq_altitudeFoot := by
    rw [cfg.D_eq_altitudeFoot]
    have hre : cfg.triangle_ABC = Simplex.reindex
        ⟨![cfg.B, cfg.A, cfg.C], cfg.affine_indep_ABC.comm_left⟩ (Equiv.swap 0 1) := by
      rw [cfg.triangle_ABC_def]
      rw [reindex]
      simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Equiv.symm_swap, Simplex.mk.injEq]
      ext x
      fin_cases x <;> rfl
    rw [hre]
    rw [Simplex.altitudeFoot_reindex]
    congr
  Sbtw_CXD := cfg.Sbtw_CXD
  Sbtw_AKX := cfg.Sbtw_BLX
  BK_eq_BC := cfg.AL_eq_AC
  Sbtw_BLX := cfg.Sbtw_AKX
  AL_eq_AC := cfg.BK_eq_BC
  M_mem_inf_AL_BK := cfg.M_mem_inf_AL_BK.symm

open scoped Affine EuclideanGeometry Real

def someOrientation [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

theorem symm_A_eq_B : cfg.symm.A = cfg.B := rfl
theorem symm_B_eq_A : cfg.symm.B = cfg.A := rfl
theorem symm_L_eq_K : cfg.symm.L = cfg.K := rfl
theorem symm_K_eq_L : cfg.symm.K = cfg.L := rfl

theorem not_col_ABC : ¬Collinear ℝ {cfg.A, cfg.B, cfg.C} :=
  affineIndependent_iff_not_collinear_set.mp cfg.affine_indep_ABC

theorem h_A : cfg.triangle_ABC.points 0 = cfg.A := by simp [cfg.triangle_ABC_def]
theorem h_B : cfg.triangle_ABC.points 1 = cfg.B := by simp [cfg.triangle_ABC_def]
theorem h_C : cfg.triangle_ABC.points 2 = cfg.C := by simp [cfg.triangle_ABC_def]

theorem X_mem_CD : cfg.X ∈ line[ℝ, cfg.C, cfg.D] := cfg.Sbtw_CXD.wbtw.mem_affineSpan

def sphere_A := EuclideanGeometry.Sphere.mk cfg.A (dist cfg.A cfg.C)
def sphere_B := EuclideanGeometry.Sphere.mk cfg.B (dist cfg.B cfg.C)

theorem sphere_a : cfg.sphere_A = EuclideanGeometry.Sphere.mk cfg.A (dist cfg.A cfg.C) := by rfl
theorem sphere_b : cfg.sphere_B = EuclideanGeometry.Sphere.mk cfg.B (dist cfg.B cfg.C) := by rfl


theorem C_mem_sphere_A : cfg.C ∈ cfg.sphere_A := by
  apply mem_sphere.mpr
  rw [EuclideanGeometry.Sphere.radius, dist_comm]
  rfl

theorem C_mem_sphere_B : cfg.C ∈ cfg.sphere_B := cfg.symm.C_mem_sphere_A

theorem dist_CA_eq_radius_A : dist cfg.C cfg.A = cfg.sphere_A.radius := by
  rw [EuclideanGeometry.Sphere.radius, dist_comm]
  rfl

theorem dist_CB_eq_radius_B : dist cfg.C cfg.B = cfg.sphere_B.radius := cfg.symm.dist_CA_eq_radius_A

def v_XK := cfg.X -ᵥ cfg.K
def v_XL := cfg.X -ᵥ cfg.L

lemma v_XK_def : cfg.X -ᵥ cfg.K = cfg.v_XK := by rfl
lemma v_XL_def : cfg.X -ᵥ cfg.L = cfg.v_XL := by rfl


theorem K_mem_sphere_B : cfg.K ∈ cfg.sphere_B := by
  apply mem_sphere.mpr
  rw [← dist_CB_eq_radius_B, dist_comm cfg.C]
  rw [← BK_eq_BC]
  rw [dist_comm cfg.B cfg.K]
  rfl

theorem L_mem_sphere_A : cfg.L ∈ cfg.sphere_A := cfg.symm.K_mem_sphere_B

def K' := cfg.sphere_B.secondInter cfg.K cfg.v_XK
def L' := cfg.sphere_A.secondInter cfg.L cfg.v_XL

lemma K'_def :  cfg.sphere_B.secondInter cfg.K cfg.v_XK = cfg.K' := by rfl
lemma L'_def :  cfg.sphere_A.secondInter cfg.L cfg.v_XL = cfg.L' := by rfl

theorem symm_K'_eq_L' : cfg.symm.K' = cfg.L' := by rfl
theorem symm_L'_eq_K' : cfg.symm.L' = cfg.K' := by rfl

theorem h_sphere_A_radius : 0 ≤ cfg.sphere_A.radius := Sphere.radius_nonneg_of_mem
    cfg.C_mem_sphere_A
theorem h_sphere_B_radius : 0 ≤ cfg.sphere_B.radius := cfg.symm.h_sphere_A_radius

theorem h_angle_CDB : ∠ cfg.C cfg.D cfg.B = π / 2 := by
  rw [cfg.D_eq_altitudeFoot]
  have h_ne: (2: Fin 3) ≠ 1 := by simp
  have := angle_point_altitudeFoot_eq_pi_div_two cfg.triangle_ABC h_ne
  rw [h_C, h_B] at this
  exact this

theorem h_angle_CDA : ∠ cfg.C cfg.D cfg.A = π / 2 := cfg.symm.h_angle_CDB

theorem h_BDX_eq_BDC : ∠ cfg.B cfg.D cfg.X = ∠ cfg.B cfg.D cfg.C := by
  apply angle_eq_of_sbtw
  exact cfg.Sbtw_CXD.symm

theorem h_ADX_eq_ADC : ∠ cfg.A cfg.D cfg.X = ∠ cfg.A cfg.D cfg.C := cfg.symm.h_BDX_eq_BDC

theorem dist_X_sphere_B : dist cfg.X cfg.sphere_B.center < cfg.sphere_B.radius := by
  rw [dist_comm]
  have : cfg.sphere_B.radius = dist cfg.B cfg.C := by rfl
  simp_rw [this, cfg.sphere_b]
  apply dist_lt_of_sbtw_of_inner_eq_zero cfg.Sbtw_CXD.symm
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  rw [← EuclideanGeometry.angle]
  rw [cfg.h_BDX_eq_BDC, angle_comm, h_angle_CDB]

theorem dist_X_sphere_A : dist cfg.X cfg.sphere_A.center < cfg.sphere_A.radius :=
  cfg.symm.dist_X_sphere_B

theorem hKXK' : Sbtw ℝ cfg.K cfg.X cfg.K' := by
  have := Sphere.sbtw_secondInter cfg.K_mem_sphere_B cfg.dist_X_sphere_B
  exact this

theorem hLXL' : Sbtw ℝ cfg.L cfg.X cfg.L' := cfg.symm.hKXK'

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
  simp only [cfg.sphere_a, cfg.sphere_b]
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

theorem h_L'_A : cfg.L' ∈ cfg.sphere_A := by
  unfold Imo2012Q5Cfg.L'
  simp only [Sphere.secondInter_mem]
  exact cfg.h_L_A

theorem h_K'_B : cfg.K' ∈ cfg.sphere_B := cfg.symm.h_L'_A

theorem pow_X_B : -cfg.sphere_B.power cfg.X = dist cfg.X cfg.K * dist cfg.X cfg.K' := by
  rw [Sphere.mul_dist_eq_neg_power_of_dist_center_le_radius cfg.h_sphere_B_radius
    cfg.hKXK'.wbtw.mem_affineSpan cfg.h_K_B cfg.h_K'_B]
  have angle_XDB: ∠ cfg.X cfg.D cfg.B = π / 2 := by
    rw [angle_comm, angle_eq_of_sbtw cfg.Sbtw_CXD.symm, angle_comm]
    exact cfg.h_angle_CDB
  suffices dist_lt : dist cfg.B cfg.X < dist cfg.B cfg.C by
    simp_rw [sphere_b]
    grind [dist_comm]
  apply dist_lt_of_sbtw_of_inner_eq_zero cfg.Sbtw_CXD.symm
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  rw [← EuclideanGeometry.angle]
  grind [angle_comm]

theorem pow_X_A : -cfg.sphere_A.power cfg.X = dist cfg.X cfg.L * dist cfg.X cfg.L' :=
  cfg.symm.pow_X_B

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
  have h:= cfg.X_mem_interior V Pt
  rw [cfg.triangle_ABC_def] at h
  exact h

theorem notcol_KXL : ¬ Collinear ℝ {cfg.K, cfg.X, cfg.L} := by
  rw [← affineIndependent_iff_not_collinear_set]
  have indep_XAB: AffineIndependent ℝ ![cfg.X, cfg.A, cfg.B] := by simp [indep_ABX]
  have h1:= affineIndependent_of_sbtw_affineIndependent indep_XAB cfg.Sbtw_AKX.symm
  have indep_XBK : AffineIndependent ℝ ![cfg.X, cfg.B, cfg.K] := by simp [h1]
  have h2 := affineIndependent_of_sbtw_affineIndependent indep_XBK cfg.Sbtw_BLX.symm
  simp [h2]

theorem L_ne_L' : cfg.L ≠ cfg.L' := cfg.hLXL'.left_ne_right

theorem K_ne_K' : cfg.K ≠ cfg.K' := cfg.hKXK'.left_ne_right

theorem h_L_interior : cfg.L ∈ cfg.triangle_ABC.interior := by
  have := cfg.Sbtw_BLX
  rw [← h_B] at this
  exact Triangle.mem_interior_of_sbtw_interior cfg.X_mem_interior this

theorem h_K_interior : cfg.K ∈ cfg.triangle_ABC.interior := by
  have := cfg.Sbtw_AKX
  rw [← h_A] at this
  exact Triangle.mem_interior_of_sbtw_interior cfg.X_mem_interior this

theorem sbtw_L'LB : Sbtw ℝ cfg.L' cfg.L cfg.B := by
  rw [sbtw_comm]
  exact sbtw_expand cfg.Sbtw_BLX cfg.hLXL'
theorem sbtw_K'KA : Sbtw ℝ cfg.K' cfg.K cfg.A := cfg.symm.sbtw_L'LB

theorem h_B_L_L' : cfg.B ∈ affineSpan ℝ {cfg.L, cfg.L'} := by
  have h1 := Sphere.secondInter_collinear cfg.sphere_A cfg.L cfg.X
  have h2:= cfg.Sbtw_BLX.wbtw.collinear
  have h3: Collinear ℝ {cfg.B, cfg.L', cfg.L, cfg.X} := by
    have h_L_ne_X : cfg.L ≠ cfg.X := cfg.Sbtw_BLX.ne_right
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne]
    · rw [cfg.v_XL_def, cfg.L'_def] at h1
      grind [Collinear.mem_affineSpan_of_mem_of_ne]
  apply h3.mem_affineSpan_of_mem_of_ne
  repeat simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  exact cfg.L_ne_L'

theorem h_A_K_K' : cfg.A ∈ affineSpan ℝ {cfg.K, cfg.K'} := cfg.symm.h_B_L_L'

theorem power_B_A : (dist cfg.B cfg.C) ^ 2 = dist cfg.B cfg.L * dist cfg.B cfg.L' := by
  apply EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant cfg.h_L_A cfg.h_L'_A
    cfg.h_B_L_L'
  rw [Set.pair_comm]
  apply EuclideanGeometry.Sphere.IsTangentAt_of_angle_eq_pi_div_two ?_ cfg.C_mem_sphere_A
  rw [sphere_a]
  exact cfg.angle_BCA

theorem power_A_B : (dist cfg.A cfg.C) ^ 2 = dist cfg.A cfg.K * dist cfg.A cfg.K' :=
  cfg.symm.power_B_A

variable [hd2 : Fact (finrank ℝ V = 2)]
theorem cosphereic_set_ω :
    Cospherical {cfg.K, cfg.K', cfg.L, cfg.L'} := by
  haveI := someOrientation V
  apply cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi cfg.notcol_KXL
  · rw [angle_eq_pi_iff_sbtw]
    exact cfg.hKXK'
  · rw [angle_eq_pi_iff_sbtw]
    exact cfg.hLXL'
  · simp [cfg.hx, dist_comm]

def sphere_ω : EuclideanGeometry.Sphere Pt :=
  (cospherical_iff_exists_sphere.mp (cosphereic_set_ω (cfg := cfg))).choose

theorem h_ω : ∀ p ∈ ({cfg.K, cfg.K', cfg.L, cfg.L'} : Set Pt) , p ∈ cfg.sphere_ω :=
  (cospherical_iff_exists_sphere.mp cfg.cosphereic_set_ω).choose_spec

theorem h_L : cfg.L ∈ cfg.sphere_ω := by simp [h_ω]
theorem h_K : cfg.K ∈ cfg.sphere_ω := by simp [h_ω]
theorem h_L' : cfg.L' ∈ cfg.sphere_ω := by simp [h_ω]
theorem h_K' : cfg.K' ∈ cfg.sphere_ω := by simp [h_ω]

theorem h_sphere_ω_radius_nonneg : 0 ≤ cfg.sphere_ω.radius := Sphere.radius_nonneg_of_mem cfg.h_L

theorem h_power_ω_B : cfg.sphere_ω.power cfg.B = dist cfg.B cfg.L * dist cfg.B cfg.L' := by
  rw [Sphere.mul_dist_eq_power_of_radius_le_dist_center cfg.h_sphere_ω_radius_nonneg cfg.h_B_L_L'
    cfg.h_L cfg.h_L']
  have h1: cfg.sphere_ω.center ∈ AffineSubspace.perpBisector cfg.L' cfg.L := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    rw [dist_comm _ cfg.L, dist_comm _ cfg.L']
    exact dist_center_eq_dist_center_of_mem_sphere cfg.h_L' cfg.h_L
  have := dist_lt_of_sbtw_of_mem_perpBisector cfg.sbtw_L'LB h1
  have h2: dist cfg.sphere_ω.center cfg.L = cfg.sphere_ω.radius := by
    rw [dist_comm]
    exact mem_sphere.mp cfg.h_L
  rw [h2, dist_comm] at this
  exact le_of_lt this

theorem h_power_ω_A : cfg.sphere_ω.power cfg.A = dist cfg.A cfg.K * dist cfg.A cfg.K' := by
  rw [Sphere.mul_dist_eq_power_of_radius_le_dist_center cfg.h_sphere_ω_radius_nonneg cfg.h_A_K_K'
  cfg.h_K cfg.h_K']
  have h1: cfg.sphere_ω.center ∈ AffineSubspace.perpBisector cfg.K' cfg.K := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    rw [dist_comm _ cfg.K, dist_comm _ cfg.K']
    exact dist_center_eq_dist_center_of_mem_sphere cfg.h_K' cfg.h_K
  have := dist_lt_of_sbtw_of_mem_perpBisector cfg.sbtw_K'KA h1
  have h2: dist cfg.sphere_ω.center cfg.K = cfg.sphere_ω.radius := by
    rw [dist_comm]
    exact mem_sphere.mp cfg.h_K
  rw [h2, dist_comm] at this
  exact le_of_lt this

theorem h_tangent_at_K_ω : cfg.sphere_ω.IsTangentAt cfg.K (line[ℝ, cfg.B, cfg.K]) := by
  rw [EuclideanGeometry.Sphere.isTangentAt_iff_dist_sq_eq_power cfg.h_K]
  rw [h_power_ω_B, cfg.BK_eq_BC]
  exact cfg.power_B_A

theorem h_tangent_at_L_ω : cfg.sphere_ω.IsTangentAt cfg.L (line[ℝ, cfg.A, cfg.L]) := by
  rw [EuclideanGeometry.Sphere.isTangentAt_iff_dist_sq_eq_power cfg.h_L]
  rw [h_power_ω_A, cfg.AL_eq_AC]
  exact cfg.power_A_B

end Imo2012Q5Cfg

end

end Imo2012Q5


open Imo2012Q5

theorem imo2012_q5 [Fact (finrank ℝ V = 2)] {A B C D X K L M : Pt}
    (affine_indep_ABC : AffineIndependent ℝ ![A, B, C])
    {triangle_ABC : Triangle ℝ Pt}
    (triangle_ABC_def : triangle_ABC = ⟨![A, B, C], affine_indep_ABC⟩)
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
    triangle_ABC_def,
    angle_BCA,
    D_eq_altitudeFoot,
    Sbtw_CXD,
    Sbtw_AKX,
    BK_eq_BC,
    Sbtw_BLX,
    AL_eq_AC,
    M_mem_inf_AL_BK
  }
  exact EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem
    cfg.h_tangent_at_K_ω (cfg.h_tangent_at_L_ω) cfg.M_mem_inf_AL_BK.2 cfg.M_mem_inf_AL_BK.1
