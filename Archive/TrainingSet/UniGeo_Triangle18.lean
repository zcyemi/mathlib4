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
    (S T V R U W : Pt)
    (AffineIndependent_STV : AffineIndependent ℝ ![S, T, V])
    (AffineIndependent_RUW : AffineIndependent ℝ ![R, U, W])
    (SVT_eq_WRU : ∠ S V T = ∠ W R U)
    (VST_eq_RWU : ∠ V S T = ∠ R W U) :
    dist S V * dist R U = dist T V * dist R W := by
  sorry
