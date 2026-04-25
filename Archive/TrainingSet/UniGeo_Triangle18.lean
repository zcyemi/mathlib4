/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib

open scoped Real EuclideanGeometry Similar Congruent InnerProductSpace
open Affine EuclideanGeometry Module AffineSubspace InnerProductSpace


variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]

/-- UniGeo_Triangle18.
In triangles STV and RUW, where angle SVT equals angle WRU, and angle VST equals
angle RWU, prove that the product of  SV and RU equals the product of
lengths TV and RW.
-/
theorem result
    (s t v r u w : Pt)
    (AffineIndependent_STV : AffineIndependent ℝ ![s, t, v])
    (AffineIndependent_RUW : AffineIndependent ℝ ![r, u, w])
    (SVT_eq_WRU : ∠ s v t = ∠ w r u)
    (VST_eq_RWU : ∠ v s t = ∠ r w u) :
    dist s v * dist r u = dist t v * dist r w := by
  have h_not_collinear_SVT : ¬Collinear ℝ ({s, v, t} : Set Pt) := by
    simpa [Set.insert_comm, Set.pair_comm] using
      (affineIndependent_iff_not_collinear_set.1 AffineIndependent_STV)
  have h_v_ne_s : v ≠ s :=
    AffineIndependent_STV.injective.ne (by decide : (2 : Fin 3) ≠ 0)
  have h_r_ne_w : r ≠ w :=
    AffineIndependent_RUW.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h_VTS_eq_RUW : ∠ v t s = ∠ r u w := by
    have hsum_SVT : ∠ s v t + ∠ v t s + ∠ t s v = π :=
      angle_add_angle_add_angle_eq_pi t h_v_ne_s
    have hsum_WRU : ∠ w r u + ∠ r u w + ∠ u w r = π :=
      angle_add_angle_add_angle_eq_pi u h_r_ne_w
    linarith [hsum_SVT, hsum_WRU, SVT_eq_WRU,
      (by simpa [angle_comm] using VST_eq_RWU : ∠ t s v = ∠ u w r)]
  have h_sim : ![s, v, t] ∼ ![w, r, u] :=
    EuclideanGeometry.similar_of_angle_angle h_not_collinear_SVT SVT_eq_WRU h_VTS_eq_RUW
  obtain ⟨k, hk_pos, hdist⟩ := h_sim.exists_pos_dist_eq
  have h_sv : dist s v = k * dist w r := by
    simpa [dist_comm] using hdist 0 1
  have h_tv : dist t v = k * dist u r := by
    simpa [dist_comm] using hdist 2 1
  rw [h_sv, h_tv]
  simp [hk_pos.ne', dist_comm, mul_assoc, mul_left_comm, mul_comm]
