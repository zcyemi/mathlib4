import Mathlib.Analysis.Convex.Hull
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
import Mathlib.Geometry.Polygon.Basic
import Mathlib.LinearAlgebra.Orientation

open Set
open scoped Affine EuclideanGeometry Real RealInnerProductSpace
open Affine EuclideanGeometry AffineSubspace Module

namespace Polygon

variable {R P : Type*} {n : ℕ}

/-- The set of vertices of a polygon. -/
def vertexSet (poly : Polygon P n) : Set P :=
  range poly

variable (R)
variable [Ring R] [LinearOrder R] [AddCommMonoid P] [Module R P]

/-- The filled region spanned by the vertices of a polygon in a module-valued ambient space. -/
def region (poly : Polygon P n) : Set P :=
  convexHull R (poly.vertexSet)

/-- The filled region of a polygon is convex by construction. -/
theorem convex_region (poly : Polygon P n) : Convex R (poly.region R) := by
  simpa [region] using convex_convexHull R (poly.vertexSet)

end Polygon

namespace EuclideanGeometry
namespace Polygon

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- A definition of strictly convex polygons in an affine space.
A polygon is strictly convex if no vertex lies within the convex hull of the remaining vertices.
This maps points to a vector space to bypass affine restrictions. -/
def IsConvexPolygon {n : ℕ} (poly : Polygon Pt n) : Prop :=
  ∀ i : Fin n,
    (0 : V) ∉ convexHull ℝ (Set.range (fun (j : {k : Fin n // k ≠ i}) => poly.vertices j.1 -ᵥ poly.vertices i))

/-- Proposition that an arbitrary n-gon is cyclic (its vertices are cospherical). -/
def IsCyclicPolygon {n : ℕ} (poly : Polygon Pt n) : Prop :=
  ∃ (center : Pt) (radius : ℝ), ∀ i : Fin n, dist (poly.vertices i) center = radius

/-- Extracts the explicit circumsphere (Sphere Pt) from the proof of a cyclic polygon. -/
noncomputable def circumsphere {n : ℕ} (poly : Polygon Pt n) (h : IsCyclicPolygon poly) : Sphere Pt where
  center := Classical.choose h
  radius := Classical.choose (Classical.choose_spec h)

/-- Core fundamental lemma: Every vertex of a cyclic polygon lies strictly on its extracted circumsphere. -/
theorem vertices_mem_circumsphere {n : ℕ} (poly : Polygon Pt n) (h : IsCyclicPolygon poly) (i : Fin n) :
    poly.vertices i ∈ (circumsphere poly h : Set Pt) := by
  have h_dist := Classical.choose_spec (Classical.choose_spec h) i
  exact Sphere.mem_coe.mpr h_dist

/--
Generic interior calculation function:
Defines the interior by constraining the range of the affine combination weights `w` to a given set `I`.
-/
def setInterior (I : Set ℝ) {n : ℕ} (poly : Polygon Pt n) : Set Pt :=
  {p | ∃ w : Fin n → ℝ,
    (∑ i, w i = 1) ∧ (∀ i, w i ∈ I) ∧ Finset.univ.affineCombination ℝ poly.vertices w = p}

/--
Strict interior of a polygon: All weights are strictly constrained to the open interval (0, 1).
Points defined this way will never fall on the edges or vertices.
-/
def interior {n : ℕ} (poly : Polygon Pt n) : Set Pt :=
  poly.setInterior (Set.Ioo 0 1)

/--
Closed interior of a polygon (equivalent to its convex hull): Weights are in the closed interval [0, 1].
-/
def closedInterior {n : ℕ} (poly : Polygon Pt n) : Set Pt :=
  poly.setInterior (Set.Icc 0 1)

/-- A parallelogram is a quadrilateral with both pairs of opposite sides parallel. -/
def IsParallelogram (q : Polygon Pt 4) : Prop :=
  line[ℝ, q 0, q 1] ∥ line[ℝ, q 2, q 3] ∧
    line[ℝ, q 1, q 2] ∥ line[ℝ, q 3, q 0]

/-- A rhombus is a parallelogram with two adjacent sides of equal length. -/
def IsRhombus (q : Polygon Pt 4) : Prop :=
  IsParallelogram q ∧ dist (q 0) (q 1) = dist (q 1) (q 2)

/-- A rectangle is a parallelogram with one right angle. -/
def IsRectangle (q : Polygon Pt 4) : Prop :=
  IsParallelogram q ∧ line[ℝ, q 0, q 1].direction ⟂ line[ℝ, q 1, q 2].direction

/-- A square is a rhombus with one right angle. -/
def IsSquare (q : Polygon Pt 4) : Prop :=
  IsRhombus q ∧ line[ℝ, q 0, q 1].direction ⟂ line[ℝ, q 1, q 2].direction

/-- A trapezoid has exactly one pair of opposite sides parallel. -/
def IsTrapezoid (q : Polygon Pt 4) : Prop :=
  line[ℝ, q 0, q 1] ∥ line[ℝ, q 2, q 3] ∧
    ¬ line[ℝ, q 1, q 2] ∥ line[ℝ, q 3, q 0]

/-- An isosceles trapezoid is a trapezoid whose legs have equal length. -/
def IsIsoscelesTrapezoid (q : Polygon Pt 4) : Prop :=
  IsTrapezoid q ∧ dist (q 0) (q 3) = dist (q 1) (q 2)


variable [Module.Oriented ℝ V (Fin 2)]

/-- Counterclockwise convex quadrilateral, encoded by the signs of the four turning angles. -/
def IsCcwConvex (q : Polygon Pt 4) : Prop :=
  (∡ (q 0) (q 1) (q 2)).sign = 1 ∧
    (∡ (q 1) (q 2) (q 3)).sign = 1 ∧
    (∡ (q 2) (q 3) (q 0)).sign = 1 ∧
    (∡ (q 3) (q 0) (q 1)).sign = 1

/-- Clockwise convex quadrilateral, encoded by the signs of the four turning angles. -/
def IsCwConvex (q : Polygon Pt 4) : Prop :=
  (∡ (q 0) (q 1) (q 2)).sign = -1 ∧
    (∡ (q 1) (q 2) (q 3)).sign = -1 ∧
    (∡ (q 2) (q 3) (q 0)).sign = -1 ∧
    (∡ (q 3) (q 0) (q 1)).sign = -1

/-- Orientation-free convex quadrilateral. -/
def IsConvex (q : Polygon Pt 4) : Prop :=
  IsCcwConvex q ∨ IsCwConvex q

abbrev IsConvexQuadrilateral (q : Polygon Pt 4) : Prop :=
  IsConvex q

/--
`IsCompleteQuadrilateral q` records the polygonal data usually needed for the associated
complete quadrilateral: the two diagonals meet at an interior point.
-/
def IsCompleteQuadrilateral (q : Polygon Pt 4) : Prop :=
  ∃ p : Pt, Sbtw ℝ (q 0) p (q 2) ∧ Sbtw ℝ (q 1) p (q 3)

private theorem not_collinear_of_sign_eq_one {A B C : Pt} (h : (∡ A B C).sign = 1) :
    ¬ Collinear ℝ ({A, B, C} : Set Pt) := by
  intro hcol
  have hne : (∡ A B C).sign ≠ 0 := by
    simp [h]
  exact hne (EuclideanGeometry.oangle_sign_eq_zero_iff_collinear.mpr hcol)

private theorem not_collinear_of_sign_eq_neg_one {A B C : Pt} (h : (∡ A B C).sign = -1) :
    ¬ Collinear ℝ ({A, B, C} : Set Pt) := by
  intro hcol
  have hne : (∡ A B C).sign ≠ 0 := by
    simp [h]
  exact hne (EuclideanGeometry.oangle_sign_eq_zero_iff_collinear.mpr hcol)

/-- In a counterclockwise convex quadrilateral, the first three consecutive vertices are not
collinear. -/
theorem IsCcwConvex.not_collinear012 {q : Polygon Pt 4} (hq : IsCcwConvex q) :
    ¬ Collinear ℝ ({q 0, q 1, q 2} : Set Pt) :=
  not_collinear_of_sign_eq_one hq.1

/-- In a counterclockwise convex quadrilateral, the second through fourth vertices are not
collinear. -/
theorem IsCcwConvex.not_collinear123 {q : Polygon Pt 4} (hq : IsCcwConvex q) :
    ¬ Collinear ℝ ({q 1, q 2, q 3} : Set Pt) :=
  not_collinear_of_sign_eq_one hq.2.1

/-- In a counterclockwise convex quadrilateral, the triples `(2,3,0)` are not collinear. -/
theorem IsCcwConvex.not_collinear230 {q : Polygon Pt 4} (hq : IsCcwConvex q) :
    ¬ Collinear ℝ ({q 2, q 3, q 0} : Set Pt) :=
  not_collinear_of_sign_eq_one hq.2.2.1

/-- In a counterclockwise convex quadrilateral, the triples `(3,0,1)` are not collinear. -/
theorem IsCcwConvex.not_collinear301 {q : Polygon Pt 4} (hq : IsCcwConvex q) :
    ¬ Collinear ℝ ({q 3, q 0, q 1} : Set Pt) :=
  not_collinear_of_sign_eq_one hq.2.2.2

/-- In a clockwise convex quadrilateral, the first three consecutive vertices are not
collinear. -/
theorem IsCwConvex.not_collinear012 {q : Polygon Pt 4} (hq : IsCwConvex q) :
    ¬ Collinear ℝ ({q 0, q 1, q 2} : Set Pt) :=
  not_collinear_of_sign_eq_neg_one hq.1

/-- In a clockwise convex quadrilateral, the second through fourth vertices are not collinear. -/
theorem IsCwConvex.not_collinear123 {q : Polygon Pt 4} (hq : IsCwConvex q) :
    ¬ Collinear ℝ ({q 1, q 2, q 3} : Set Pt) :=
  not_collinear_of_sign_eq_neg_one hq.2.1

/-- In a clockwise convex quadrilateral, the triples `(2,3,0)` are not collinear. -/
theorem IsCwConvex.not_collinear230 {q : Polygon Pt 4} (hq : IsCwConvex q) :
    ¬ Collinear ℝ ({q 2, q 3, q 0} : Set Pt) :=
  not_collinear_of_sign_eq_neg_one hq.2.2.1

/-- In a clockwise convex quadrilateral, the triples `(3,0,1)` are not collinear. -/
theorem IsCwConvex.not_collinear301 {q : Polygon Pt 4} (hq : IsCwConvex q) :
    ¬ Collinear ℝ ({q 3, q 0, q 1} : Set Pt) :=
  not_collinear_of_sign_eq_neg_one hq.2.2.2

/-- Any convex quadrilateral has its first three consecutive vertices noncollinear. -/
theorem IsConvex.not_collinear012 {q : Polygon Pt 4} (hq : IsConvex q) :
    ¬ Collinear ℝ ({q 0, q 1, q 2} : Set Pt) := by
  rcases hq with hq | hq
  · exact hq.not_collinear012
  · exact hq.not_collinear012

/-- Any convex quadrilateral has its second through fourth vertices noncollinear. -/
theorem IsConvex.not_collinear123 {q : Polygon Pt 4} (hq : IsConvex q) :
    ¬ Collinear ℝ ({q 1, q 2, q 3} : Set Pt) := by
  rcases hq with hq | hq
  · exact hq.not_collinear123
  · exact hq.not_collinear123

/-- Any convex quadrilateral has the triple `(2,3,0)` noncollinear. -/
theorem IsConvex.not_collinear230 {q : Polygon Pt 4} (hq : IsConvex q) :
    ¬ Collinear ℝ ({q 2, q 3, q 0} : Set Pt) := by
  rcases hq with hq | hq
  · exact hq.not_collinear230
  · exact hq.not_collinear230

/-- Any convex quadrilateral has the triple `(3,0,1)` noncollinear. -/
theorem IsConvex.not_collinear301 {q : Polygon Pt 4} (hq : IsConvex q) :
    ¬ Collinear ℝ ({q 3, q 0, q 1} : Set Pt) := by
  rcases hq with hq | hq
  · exact hq.not_collinear301
  · exact hq.not_collinear301

section
set_option linter.unusedSectionVars false
/-- A complete quadrilateral has a genuine intersection point for its diagonals. -/
theorem IsCompleteQuadrilateral.exists_diagonal_intersection {q : Polygon Pt 4}
    (hq : IsCompleteQuadrilateral q) :
    ∃ p : Pt, p ∈ line[ℝ, q 0, q 2] ⊓ line[ℝ, q 1, q 3] := by
  rcases hq with ⟨p, hp02, hp13⟩
  exact ⟨p, hp02.wbtw.mem_affineSpan, hp13.wbtw.mem_affineSpan⟩

/-- In a complete quadrilateral, the diagonal intersection determines two straight angles. -/
theorem IsCompleteQuadrilateral.angle_eq_pi {q : Polygon Pt 4} (hq : IsCompleteQuadrilateral q) :
    ∃ p : Pt, ∠ (q 0) p (q 2) = π ∧ ∠ (q 1) p (q 3) = π := by
  rcases hq with ⟨p, hp02, hp13⟩
  exact ⟨p, hp02.angle₁₂₃_eq_pi, hp13.angle₁₂₃_eq_pi⟩
end

/-- Ptolemy's theorem for a cyclic quadrilateral whose diagonals meet internally. -/
theorem IsCyclic.ptolemy {q : Polygon Pt 4} (hq : IsCyclicPolygon q)
    (hcomplete : IsCompleteQuadrilateral q) :
    dist (q 0) (q 1) * dist (q 2) (q 3) + dist (q 1) (q 2) * dist (q 3) (q 0) =
      dist (q 0) (q 2) * dist (q 1) (q 3) := by
  rcases hcomplete.angle_eq_pi with ⟨p, hp02, hp13⟩
  apply EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical
      (a := q 0) (b := q 1) (c := q 2) (d := q 3) (p := p)
  unfold IsCyclicPolygon at hq
  rw [Cospherical]
  · obtain ⟨center, radius, h⟩ := hq
    refine ⟨center, radius, ?_⟩
    aesop
  exact hp02
  exact hp13

end Polygon
end EuclideanGeometry
