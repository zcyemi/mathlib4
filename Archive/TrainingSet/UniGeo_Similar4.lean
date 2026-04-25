/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib
open scoped Real EuclideanGeometry Similar
open Affine EuclideanGeometry Module AffineSubspace

namespace Similar4

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]


/-- UniGeo_Similar4. In triangles EFI and GHI, where I lies between E and G, I lies between H and
F, and angle HGI equals angle FEI, prove that triangles EIF and GIH are similar.
-/
theorem result
    (E F I G H : Pt)
    (AffiIndependent_EFI : AffineIndependent ℝ ![E, F, I])
    (AffiIndependent_GHI : AffineIndependent ℝ ![G, H, I])
    (Sbtw_EIG : Sbtw ℝ E I G)
    (Sbtw_HIF : Sbtw ℝ H I F)
    (HGI_eq_FEI : ∠ H G I = ∠ F E I) :
    ![E, I, F] ∼ ![G, I, H] := by
  have h_not_collinear_EIF : ¬Collinear ℝ ({E, I, F} : Set Pt) := by
    simpa [Set.insert_comm, Set.pair_comm] using
      (affineIndependent_iff_not_collinear_set.1 AffiIndependent_EFI)
  have h_G_ne_H : G ≠ H :=
    AffiIndependent_GHI.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h_E_ne_I : E ≠ I :=
    AffiIndependent_EFI.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h_EIG_pi : ∠ E I G = π := by
    exact angle_eq_pi_iff_sbtw.mpr Sbtw_EIG
  have h_FIH_pi : ∠ F I H = π := by
    simpa [angle_comm] using (angle_eq_pi_iff_sbtw.mpr Sbtw_HIF)
  have h_EIF_eq_GIH : ∠ E I F = ∠ G I H := by
    exact angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h_EIG_pi h_FIH_pi
  have h_IFE_eq_IHG : ∠ I F E = ∠ I H G := by
    have hsum_EIF : ∠ F E I + ∠ E I F + ∠ I F E = π := by
      have h1 := angle_add_angle_add_angle_eq_pi F h_E_ne_I
      grind [angle_comm]
    have hsum_GIH : ∠ H G I + ∠ G I H + ∠ I H G = π := by
      have h1 := angle_add_angle_add_angle_eq_pi I h_G_ne_H
      grind
    linarith [hsum_EIF, hsum_GIH, HGI_eq_FEI, h_EIF_eq_GIH]
  exact EuclideanGeometry.similar_of_angle_angle h_not_collinear_EIF h_EIF_eq_GIH h_IFE_eq_IHG

end Similar4
