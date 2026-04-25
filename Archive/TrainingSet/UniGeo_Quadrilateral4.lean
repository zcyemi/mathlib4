/-
Copyright (c) 2026 Wang Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Ying
-/
import Mathlib
import EuclideanGeometry.Definition.Polygon

open scoped Real EuclideanGeometry Similar Congruent InnerProductSpace
open Affine EuclideanGeometry Module AffineSubspace InnerProductSpace

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Oriented ℝ V (Fin 2)]

/-- UniGeo_Quadrilateral4.
In quadrilateral GHJI with diagonal GJ, where length IJ equals length GH, and
lines GH and IJ are parallel, prove that length HJ equals length GI.
-/
theorem result
    (G H J I : Pt)
    (GHJI : Polygon Pt 4)
    (G_def : G = GHJI 0)
    (H_def : H = GHJI 1)
    (J_def : J = GHJI 2)
    (I_def : I = GHJI 3)
    (IJ_eq_GH : dist I J = dist G H)
    (GH_parallel_IJ : line[ℝ, G, H] ∥ line[ℝ, I, J]) :
    dist H J = dist G I := by
  sorry
