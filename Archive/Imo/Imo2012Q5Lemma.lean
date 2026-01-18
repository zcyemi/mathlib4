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

open AffineSubspace

open InnerProductGeometry


open scoped Finset

variable [AddCommMonoid Pt] [SMul ℝ Pt]

namespace EuclideanGeometry.Sphere


end EuclideanGeometry.Sphere


section
open scoped EuclideanGeometry Real
open EuclideanGeometry


end

end

end Lemma
