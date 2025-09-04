import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Geometry.Euclidean.Sphere.RadicalAxis
import Mathlib.Geometry.Euclidean.Altitude

open EuclideanGeometry Real
open Affine Module



namespace IMO2012Q5

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]



-- def RadicalAxis (s1 s2 : EuclideanGeometry.Sphere P) : AffineSubspace ℝ P :=
--   let ps := {x : P | s1.power x = s2.power x}
--   AffineSubspace.mk

theorem cospherical_of_mul_dist_eq_mul_dist {a b c d p : P}
    (hapb : ∃ k₁ : ℝ, k₁ ≠ 1 ∧ b -ᵥ p = k₁ • (a -ᵥ p))
    (hcpd : ∃ k₂ : ℝ, k₂ ≠ 1 ∧ d -ᵥ p = k₂ • (c -ᵥ p))
    (h : dist a p * dist b p = dist c p * dist d p) :
    Cospherical ({a, b, c, d} : Set P) := by
  sorry


theorem result {A B C D X K L M : P}
  (affine_indep_ABC : AffineIndependent ℝ ![A, B, C])
  {triangle_ABC : Triangle ℝ P}
  (h_triange_eq : triangle_ABC = ⟨![A, B, C], affine_indep_ABC⟩)
  (angle_BCA : ∠ B C A = π / 2)
  (D_eq_altitudeFoot : D = triangle_ABC.altitudeFoot 2)
  (X_mem_CD : X ∈ line[ℝ, C, D])
  (K_mem_AX : K ∈ line[ℝ, A, X])
  (BK_eq_BC : dist B K = dist B C)
  (L_mem_BX : L ∈ line[ℝ, B, X])
  (AL_eq_AC : dist A L = dist A C)
  (M_mem_inf_AL_BK : M ∈ line[ℝ, A, L] ⊓ line[ℝ, B, K]) :
  dist M K = dist M L := by

  set sphere_A :=EuclideanGeometry.Sphere.mk A (dist A C) with sphere_A_def
  set sphere_B :=EuclideanGeometry.Sphere.mk B (dist B C) with sphere_B_def

  set v_AX := (K -ᵥ A) with v_AX_def
  set v_BX := (L -ᵥ B) with v_BX_def

  set K' := sphere_B.secondInter K v_AX with K'_def
  set L' := sphere_A.secondInter L v_BX with L'_def

  have h_CD_radical_axis : Sphere.radicalAxis sphere_A sphere_B = line[ℝ, C, D] := by
    sorry

  have pow_X_eq : sphere_A.power X = sphere_B.power X := by
    apply Sphere.mem_radicalAxis_pow_eq
    rw [h_CD_radical_axis]
    exact X_mem_CD

  have pow_X_B : sphere_B.power X = dist X K * dist X K' := by
    sorry

  have pow_X_A : sphere_A.power X = dist X L * dist X L' := by
    sorry

  have hx : dist X K * dist X K' = dist X L * dist X L' := by
    rw [← pow_X_A, ← pow_X_B, pow_X_eq]

  set set_ω : Set P := {K, L, K', L'} with set_ω_def

  have cosphereic_set_ω : Cospherical set_ω := by
    sorry

  -- def sphere omega
  have h_omega := cospherical_iff_exists_sphere.mp cosphereic_set_ω
  obtain ⟨sphere_ω, h_ω⟩ := h_omega

  have power_B_A : (dist B C) ^ 2  = dist B L * dist B L' := by
    have h_L : L ∈ sphere_ω := by sorry
    apply EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant h_L
    repeat sorry

  have power_A_B : (dist A C) ^ 2  = dist A K * dist A K' := by
    have h_K : K ∈ sphere_ω := by sorry
    apply EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant h_K
    repeat sorry

  rw [← BK_eq_BC] at power_B_A
  rw [← AL_eq_AC] at power_A_B

  set line_BK := line[ℝ, B, K] with line_BK_def
  set line_AL := line[ℝ, A, L] with line_AL_def
  have h_tangent_at_K_ω : sphere_ω.IsTangentAt K line_BK := by
    sorry

  have h_tangent_at_L_ω : sphere_ω.IsTangentAt L line_AL := by
    sorry

  -- tangent dist eq
  sorry


end IMO2012Q5
