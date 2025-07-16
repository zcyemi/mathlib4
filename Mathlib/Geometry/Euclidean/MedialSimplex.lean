import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Centroid

import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.LinearAlgebra.AffineSpace.MidpointZero

noncomputable section

namespace Affine

namespace Simplex

open EuclideanGeometry
open Finset


variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable {n : ℕ} [NeZero n]

lemma faceOppositeCentroid_indepdent (s : Affine.Simplex ℝ P n)
    {spoints : Fin (n + 1) → P} (hs : spoints = (fun i => s.faceOppositeCentroid i)) :
    AffineIndependent ℝ spoints := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ spoints 0, hs]
  simp only [ne_eq]
  have h : LinearIndependent ℝ fun (i : { x // x ≠ 0 }) ↦ ((1:ℝ) / n) •
      (s.points 0 -ᵥ s.points i.val) := by
    have hx := s.independent
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0] at hx
    let f : V →ₗ[ℝ] V := (-((1:ℝ) / n)) • LinearMap.id
    have hmap := hx.map' f (by rw [LinearMap.ker_smul _ _
        (by simp [NeZero.ne n]), LinearMap.ker_id])
    convert hmap with x
    simp only [f, one_div, ne_eq, neg_smul, Function.comp_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [←neg_vsub_eq_vsub_rev, smul_neg]
  grind [faceOppositeCentroid_vsub_faceOppositeCentroid]


def medialSimplex (s : Affine.Simplex ℝ P n) : Affine.Simplex ℝ P n :=
  let spoints := (fun i => s.faceOppositeCentroid i)
  ⟨spoints, faceOppositeCentroid_indepdent s rfl⟩



theorem medialSimplex_centroid_eq_centroid (s : Affine.Simplex ℝ P n) :
    s.medialSimplex.centroid = s.centroid := by
  unfold medialSimplex
  unfold centroid
  simp

  sorry



def medialSimplexCircumsphere (s : Affine.Simplex ℝ P n) : Sphere P :=
  s.medialSimplex.circumsphere


def medialSimplexCircumcenter (s : Affine.Simplex ℝ P n) : P :=
  s.medialSimplex.circumcenter

theorem medialSimplexCircumcenter_eq_lineMap_mongePoint_circumcenter (s : Affine.Simplex ℝ P n) :
    s.medialSimplexCircumcenter =
    AffineMap.lineMap (s.mongePoint) (s.circumcenter) ((1:ℝ) / n) := by
  rw [AffineMap.lineMap_apply]



theorem medialSimplexCircumcenter_eq_lineMap_circumcenter_centroid (s : Affine.Simplex ℝ P n) :
    s.medialSimplexCircumcenter = AffineMap.lineMap (s.circumcenter) (s.centroid) (n+1:ℝ) := by
  sorry

theorem wbtw_circumcenter_medialSimplexCircumcenter_mongepoint (s : Affine.Simplex ℝ P n) :
    Wbtw ℝ s.circumcenter s.medialSimplexCircumcenter s.mongePoint := by
  sorry


theorem medialSimplexCircumcenter_mem_affineSegment (s : Affine.Simplex ℝ P n) :
    s.medialSimplexCircumcenter ∈ affineSegment ℝ s.mongePoint s.circumcenter := by
  sorry

theorem collinear_medialSimplexCircumcenter_mongePoint_circumcenter_centroid
    (s : Affine.Simplex ℝ P n) :
    Collinear ℝ {s.medialSimplexCircumcenter, s.mongePoint, s.circumcenter, s.centroid} := by
  sorry

-- 3(n+1) points of faceOppositeCentroid
theorem faceOppositeCentroid_mem_medialSimplexSphere (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.medialSimplexCircumsphere := by
  apply mem_circumsphere

def pointOfMongePointVertex (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) : P :=
  AffineMap.lineMap s.mongePoint (s.points i) ((1:ℝ) / n)

-- 3(n+1) points of pointOfMongePointVertex
theorem pointLineMapOfMongePointVertex_mem_medialSimplexSphere (s : Affine.Simplex ℝ P n)
    (i : Fin (n + 1)) :
    s.pointOfMongePointVertex i ∈ s.medialSimplexCircumsphere := by
    sorry

theorem collinear_pointLineMapOfMongePointVertex_medialSimplexCircumcenter_faceOppositeCentroid
    (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :
    Collinear ℝ {s.pointOfMongePointVertex i, s.medialSimplexCircumcenter,
      s.faceOppositeCentroid i} := by
  sorry

theorem pointOfMongePointVertex_orthogonalProjection_mem_medialSimplexSphere
    (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :
    ↑(orthogonalProjection (affineSpan ℝ (s.points '' {i}ᶜ)) (s.pointOfMongePointVertex i)) ∈
      s.medialSimplexCircumsphere := by
  sorry

end Simplex

namespace Triangle

open Affine AffineSubspace Module EuclideanGeometry Simplex Finset

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

abbrev ninePointCircle (t : Triangle ℝ P) : Sphere P :=
  t.medialSimplexCircumsphere

abbrev ninePointCirclecenter (t : Triangle ℝ P) : P :=
  t.medialSimplexCircumcenter

theorem ninePointCircumcenter_eq_midpoint (t : Triangle ℝ P) :
    t.ninePointCirclecenter = midpoint ℝ t.circumcenter t.orthocenter := by
  sorry

theorem ninePointCircle_radius_eq_half_circumradius (t : Triangle ℝ P) :
    t.ninePointCircle.radius = (1 / 2) * t.circumradius := by
  sorry

/-- The midpoint of edges on nine-point circle, which is proof by the definition of medial simplex
sphere. -/
theorem edge_midpoint_mem_ninePointCircle (t : Triangle ℝ P) (i j : Fin 3) (h : i ≠ j) :
    midpoint ℝ (t.points i) (t.points j) ∈ t.ninePointCircle := by
  unfold ninePointCircle
  have hk : ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ {k} ∪ {i, j} = Finset.univ := by decide +revert
  obtain ⟨k, hk1, hk2, hk3⟩ := hk
  have hface : t.faceOppositeCentroid k = midpoint ℝ (t.points i) (t.points j) := by
    unfold faceOppositeCentroid Simplex.centroid
    have : Finset.centroid ℝ Finset.univ (faceOpposite t k).points  =
      Finset.centroid ℝ {i, j} (t.points) := by
      rw [faceOpposite, face_centroid_eq_centroid]
      rw [compl_eq_univ_sdiff, ← hk3, union_comm, union_sdiff_cancel_right]
      simp [hk1,hk2]
    rw [this, centroid_pair, inv_eq_one_div, one_div, ← invOf_eq_inv, ← midpoint_vsub_left,
      vsub_vadd]
  rw [← hface]
  exact t.faceOppositeCentroid_mem_medialSimplexSphere k

/-- Midpoint of triangle vertex and triangle orthocenter is the `pointOfMongePointVertex` on the
medialSimplexCircumsphere. -/
theorem midpoint_vertex_orthocenter_mem_ninePointCircle (t : Triangle ℝ P) (i : Fin 3) :
    midpoint ℝ (t.points i) t.orthocenter ∈ t.ninePointCircle := by
  have h : t.pointOfMongePointVertex i = midpoint ℝ (t.points i) t.orthocenter := by
    unfold pointOfMongePointVertex
    rw [Nat.cast_ofNat, one_div, lineMap_inv_two, midpoint_comm, orthocenter]
  rw [←h]
  exact t.pointLineMapOfMongePointVertex_mem_medialSimplexSphere i

theorem pointOfMongePointVertex_mem_altitude (t : Triangle ℝ P) (i : Fin 3) :
    t.pointOfMongePointVertex i ∈ t.altitude i := by
  apply t.affineSpan_orthocenter_point_le_altitude i
  rw [orthocenter]
  unfold pointOfMongePointVertex
  exact AffineMap.lineMap_mem _ (mem_affineSpan ℝ (by simp)) (mem_affineSpan ℝ (by simp))

/-- Altitude foot is the orthogonal projection of the `pointOfMongePointVertex` on the opposite
edge, on triangle (Simplex dimension 2), the mongePoint is the orthocenter, so the line mongePoint
to vertex is the altitude, and the foot of the altitude is the orthogonal projection of the vertex
and `pointOfMongePointVertex`. -/
theorem altitude_foot_mem_ninePointCircle (t : Triangle ℝ P) (i : Fin 3) :
    t.altitudeFoot i ∈ t.ninePointCircle := by
  rw [altitudeFoot_eq_orthogonalProjection_of_point_mem_altitude t i
    (t.pointOfMongePointVertex_mem_altitude i)]
  simp only [orthogonalProjectionSpan, range_faceOpposite_points]
  exact t.pointOfMongePointVertex_orthogonalProjection_mem_medialSimplexSphere i

end Triangle

end Affine
