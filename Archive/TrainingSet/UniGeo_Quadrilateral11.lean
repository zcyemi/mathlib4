/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib
import Mathlib.EG.Polygon

open scoped Real EuclideanGeometry Similar Congruent InnerProductSpace
open Affine EuclideanGeometry Module AffineSubspace InnerProductSpace



variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]

/-- UniGeo_Quadrilateral1.
In quadrilateral STVU, where length UV equals length SU, and angle SUT equals
angle VUT, prove that length ST equals length TV.
-/
theorem result
    (s t v u : Pt)
    (STVU : Polygon Pt 4)
    (s_def : s = STVU 0)
    (t_def : t = STVU 1)
    (v_def : v = STVU 2)
    (u_def : u = STVU 3)
    (uv_eq_su : dist u v = dist s u)
    (sut_eq_vut : ∠ s u t = ∠ v u t) :
    dist s t = dist t v := by
  let _ := STVU
  let _ := s_def
  let _ := t_def
  let _ := v_def
  let _ := u_def
  have h_su_eq_vu : dist s u = dist v u := by
    simpa [dist_comm] using uv_eq_su.symm
  have h_congr : ![s, u, t] ≅ ![v, u, t] :=
    EuclideanGeometry.side_angle_side sut_eq_vut h_su_eq_vu rfl
  simpa [dist_comm] using h_congr.dist_eq 0 2
