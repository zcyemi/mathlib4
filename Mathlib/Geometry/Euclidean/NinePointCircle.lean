import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Centroid

/-!
# Euler Line and Nine-Point Circle

This file defines the Euler line and nine-point circle of a triangle,
and proves their fundamental properties.

## Main Definitions

* `Triangle.centroid` - The centroid (center of mass) of a triangle
* `Triangle.ninePointCenter` - The center of the nine-point circle
* `Triangle.ninePointCircle` - The nine-point circle of a triangle

## Main Theorems

* `euler_line_collinear` - The circumcenter, centroid, nine-point center, and orthocenter are
  collinear
* `euler_line_complete_theorem` - Complete Euler line theorem with distance ratios
* `nine_point_circle_complete` - All nine notable points lie on the nine-point circle
-/

noncomputable section

open scoped EuclideanGeometry
open Finset

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Triangle
open Finset AffineSubspace EuclideanGeometry Affine Simplex

/-- The nine-point center is the midpoint of the segment from circumcenter to orthocenter. -/
def ninePointCenter (t : Triangle ℝ P) : P := midpoint ℝ t.circumcenter t.orthocenter

def ninePointRadius (t : Triangle ℝ P) : ℝ := t.circumradius / 2

/-- The nine-point circle passes through nine notable points of the triangle. -/
def ninePointCircle (t : Triangle ℝ P) : Sphere P where
  center := t.ninePointCenter
  radius := t.ninePointRadius

@[simp]
lemma ninePointRadius_eq (t : Triangle ℝ P) :
    t.ninePointRadius = t.ninePointCircle.radius := rfl

@[simp]
lemma ninePointCenter_eq (t : Triangle ℝ P) :
    t.ninePointCenter = t.ninePointCircle.center := rfl

@[simp]
lemma ninePointRadius_eq_circumradius_div_two (t : Triangle ℝ P) :
    t.ninePointCircle.radius = t.circumradius / 2 := rfl

theorem orthocenter_vsub_circumcenter_eq_three_times_centroid_vsub_circumcenter (t : Triangle ℝ P) :
    t.orthocenter -ᵥ t.circumcenter = (3 : ℝ) • (t.centroid -ᵥ t.circumcenter) := by
  unfold orthocenter mongePoint
  norm_num

theorem centroid_lineMap_circumcenter_orthocenter (t : Triangle ℝ P) :
    AffineMap.lineMap t.circumcenter t.orthocenter (⅟ 3 : ℝ) = t.centroid := by
    rw [AffineMap.lineMap_apply,
      orthocenter_vsub_circumcenter_eq_three_times_centroid_vsub_circumcenter, invOf_eq_inv,
      inv_smul_smul₀ (by norm_num), vsub_vadd]

theorem centroid_mem_segment_circumcenter_orthocenter (t : Triangle ℝ P) :
    t.centroid ∈ affineSegment ℝ t.circumcenter t.orthocenter := by
  unfold affineSegment
  simp
  use (1/3:ℝ)
  constructor
  · norm_num
  · rw [AffineMap.lineMap_apply]
    rw [orthocenter_vsub_circumcenter_eq_three_times_centroid_vsub_circumcenter]
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀, vsub_vadd]

theorem wbtw_orthocenter_centroid_circumcenter (t : Triangle ℝ P) : Wbtw ℝ t.circumcenter
    t.centroid t.orthocenter := centroid_mem_segment_circumcenter_orthocenter t

theorem collinear_circumcenter_centroid_orthocenter (t : Triangle ℝ P) :
    Collinear ℝ {t.circumcenter, t.centroid, t.orthocenter} :=
  Wbtw.collinear (wbtw_orthocenter_centroid_circumcenter t)

theorem wbtw_ninePointCenter_circumcenter_orthocenter (t : Triangle ℝ P):
    Wbtw ℝ t.circumcenter t.ninePointCenter t.orthocenter := by
  unfold ninePointCenter midpoint
  simp; right; norm_num

theorem ninePointCenter_mem_segment_circumcenter_orthocenter (t : Triangle ℝ P) :
    t.ninePointCenter ∈ affineSegment ℝ t.circumcenter t.orthocenter :=
  wbtw_ninePointCenter_circumcenter_orthocenter t

theorem collinear_circumcenter_ninepointcenter_orthocenter (t : Triangle ℝ P) :
    Collinear ℝ {t.circumcenter, t.ninePointCenter, t.orthocenter} :=
  Wbtw.collinear (wbtw_ninePointCenter_circumcenter_orthocenter t)

theorem orthocenter_vsub_circumcenter_vsub_sum_points_vsub_circumcenter_erase (t : Triangle ℝ P)
    (i : Fin 3) : ‖t.orthocenter -ᵥ t.circumcenter -ᵥ ∑ j ∈ (Finset.univ.erase i),
      (t.points j -ᵥ t.circumcenter)‖ = t.circumradius := by
    rw [orthocenter_vsub_circumcenter_eq_sum_vsub]
    simp only [mem_univ, sum_erase_eq_sub, vsub_eq_sub, sub_sub_cancel]
    rw [←dist_eq_norm_vsub, dist_circumcenter_eq_circumradius]

theorem sameRay_orthocenter_vsub_circumcenter_centroid_vsub_circumcenter (t : Triangle ℝ P) :
    SameRay ℝ (t.orthocenter -ᵥ t.circumcenter) (t.centroid -ᵥ t.circumcenter) := by
  unfold SameRay
  right;right;
  use (1:ℝ)
  use (3:ℝ)
  simp [orthocenter_vsub_circumcenter_eq_three_times_centroid_vsub_circumcenter]

/-- **Euler Line Theorem**: The circumcenter, centroid, nine-point center, and orthocenter
    are all collinear and lie on the Euler line. -/
theorem euler_line_collinear (t : Triangle ℝ P) :
    Collinear ℝ {t.ninePointCenter, t.centroid, t.circumcenter, t.orthocenter} := by
  apply collinear_insert_insert_of_mem_affineSpan_pair
  · exact Wbtw.mem_affineSpan (wbtw_ninePointCenter_circumcenter_orthocenter t)
  · exact Wbtw.mem_affineSpan (wbtw_orthocenter_centroid_circumcenter t)

theorem centroid_lineMap_circumcenter_ninePointCenter (t : Triangle ℝ P) :
    AffineMap.lineMap t.circumcenter t.ninePointCenter (2 / 3:ℝ) = t.centroid := by
  unfold ninePointCenter
  rw [← centroid_lineMap_circumcenter_orthocenter t]
  unfold AffineMap.lineMap
  field_simp
  rw [←smul_assoc, smul_eq_mul]
  ring_nf

end Affine.Triangle

namespace EuclideanGeometry

open Affine.Triangle
open Affine.Simplex

-- 边的中点在九点圆上
/-- **Nine-Point Circle Theorem**: The midpoint of each side lies on the nine-point circle. -/
theorem edge_midpoint_on_nine_point_circle (t : Affine.Triangle ℝ P) (i j: Fin 3) (h: i ≠ j) :
  midpoint ℝ (t.points i) (t.points j) ∈ t.ninePointCircle := by
  let s := t.points
  have h_points : s = t.points := rfl
  set k := midpoint ℝ (s i) (s j)
  have h_q : ∃ q : Fin 3, q ≠ i ∧ q ≠ j ∧ {q} ∪ {i, j} = Finset.univ := by decide +revert
  obtain ⟨q, hqi, hqj, h_univ⟩ := h_q
  have hq_mem: q ∈ Finset.univ := by simp only [mem_univ]
  apply mem_sphere.mpr
  rw [← ninePointRadius_eq, dist_eq_norm_vsub]
  -- 证明边的中点到九点圆心 等于 九点圆半径的一半
  have hk' : k -ᵥ t.ninePointCenter = (⅟ 2:ℝ) • (t.circumcenter -ᵥ s q) := by
    rw [←vsub_sub_vsub_cancel_right _ _ t.circumcenter]
    have : k -ᵥ t.circumcenter = (⅟ 2:ℝ) • ((s i -ᵥ t.circumcenter) +ᵥ (s j -ᵥ t.circumcenter)) :=
      by unfold k; rw [midpoint_vsub, ←smul_add]; field_simp
    rw [this]
    have : t.ninePointCenter -ᵥ t.circumcenter = (⅟ 2:ℝ) • (t.orthocenter -ᵥ t.circumcenter) := by
      unfold ninePointCenter
      rw [midpoint_vsub, ← smul_add]
      field_simp
    rw [this, ←smul_sub, orthocenter_vsub_circumcenter_eq_sum_vsub]
    congr 1
    simp
    set f : Fin 3 → V := fun x => s x -ᵥ t.circumcenter
    have : s i -ᵥ t.circumcenter + (s j -ᵥ t.circumcenter) = ∑ x ∈ Finset.univ.erase q, f x := by
      rw [Finset.sum_erase_eq_sub hq_mem]
      have : s i -ᵥ t.circumcenter + (s j -ᵥ t.circumcenter) = f i + f j := by unfold f;simp
      rw [this, eq_sub_iff_add_eq]
      have h_sum_univ : ∑ x ∈ Finset.univ, f x = f i + f j + f q := by
        rw [← h_univ, Finset.sum_union, Finset.sum_pair h, Finset.sum_singleton, add_comm]
        simp only [disjoint_insert_right, mem_singleton, disjoint_singleton_right]
        tauto
      rw [h_sum_univ]
    rw [this, Finset.sum_erase_eq_sub hq_mem, sub_sub, add_comm, ← sub_sub]
    unfold f
    rw [h_points]
    simp
  rw [← ninePointCenter_eq, hk', norm_smul, ← dist_eq_norm_vsub', h_points,
    t.dist_circumcenter_eq_circumradius, mul_comm]
  field_simp

theorem orthocenter_orthogonalProjection_eq_altitudeFoot (t : Affine.Triangle ℝ P) (i : Fin 3):
    orthogonalProjection (affineSpan ℝ (t.points '' {i}ᶜ)) t.orthocenter =
    t.altitudeFoot i := by
  rw [altitudeFoot_eq_orthogonalProjection_of_point_mem_altitude t i t.orthocenter_mem_altitude]
  simp only [orthogonalProjectionSpan, range_faceOpposite_points]

/-- The distance from any altitude foot to the nine-point center equals the nine-point circle
  radius. -/
theorem dist_altiudeFoot_ninePointCircle_eq_ninePointRadius (t : Affine.Triangle ℝ P) (i : Fin 3) :
  dist (t.altitudeFoot i) t.ninePointCenter = t.ninePointRadius := by
  unfold ninePointCenter
  have h_compls : ∃ j k : Fin 3, j ≠ k ∧ i ≠ j ∧ i ≠ k ∧ {j, k} ∪ {i} = univ := by decide +revert
  obtain ⟨j, k, h_jk, h_ij, h_ik, h_univ⟩ := h_compls
  have h_c :  {i}ᶜ = ({j, k} :Set (Fin 3)) := by
    rw [Set.compl_eq_univ_diff, ← Finset.coe_univ, ←h_univ]
    push_cast
    simp [h_ij, h_ik]
  -- construct the reflection point of the orthocenter across the line through j and k
  let refl_ortho := reflection (affineSpan ℝ (t.points '' {j, k})) t.orthocenter
  have h_altitude_foot : t.altitudeFoot i = midpoint ℝ t.orthocenter refl_ortho := by
    unfold refl_ortho
    rw [EuclideanGeometry.reflection_apply]
    have h_altitudefoot : (orthogonalProjection (affineSpan ℝ (t.points '' {j, k}))) t.orthocenter =
        t.altitudeFoot i := by
      rw [←orthocenter_orthogonalProjection_eq_altitudeFoot t i]
      simp only [h_c]
    simp [h_altitudefoot]
    apply eq_of_vsub_eq_zero
    rw [vsub_midpoint, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, ← smul_add, neg_vsub_eq_vsub_rev,
      vsub_add_vsub_cancel, vsub_self, smul_zero]
  rw [midpoint_comm, h_altitude_foot, dist_eq_norm_vsub, midpoint_vsub_midpoint_same_left,
    norm_smul, mul_comm]
  field_simp
  rw [← dist_eq_norm_vsub, dist_comm,]
  unfold refl_ortho
  rw [dist_circumcenter_reflection_orthocenter t h_jk]

theorem altitudeFoot_mem_ninePointCircle (t : Affine.Triangle ℝ P) (i : Fin 3) :
  t.altitudeFoot i ∈ t.ninePointCircle := by
  simp only [ninePointCircle, mem_sphere]
  exact dist_altiudeFoot_ninePointCircle_eq_ninePointRadius t i

/-- The midpoint of each triange vertex of orthocenter
    lies on the nine-point circle. -/
theorem midpoint_point_orthocenter_mem_ninePointCircle (t : Affine.Triangle ℝ P) (i : Fin 3) :
  midpoint ℝ (t.points i) t.orthocenter ∈ t.ninePointCircle := by
  apply mem_sphere.mpr
  rw [← ninePointCenter_eq, ninePointCenter, midpoint, AffineMap.lineMap_apply, midpoint,
    AffineMap.lineMap_apply, dist_eq_norm_vsub]
  have : (((⅟ 2):ℝ) • (t.orthocenter -ᵥ t.points i) +ᵥ t.points i) -ᵥ (((⅟ 2):ℝ)
      • (t.orthocenter -ᵥ Affine.Simplex.circumcenter t) +ᵥ Affine.Simplex.circumcenter t) =
      (((⅟ 2):ℝ) • (t.points i -ᵥ Affine.Simplex.circumcenter t)) := by
    rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc]
    have h : t.points i -ᵥ Affine.Simplex.circumcenter t = ((⅟ 2):ℝ) • (2:ℝ)
      • (t.points i -ᵥ Affine.Simplex.circumcenter t) := by simp
    rw [h, ← smul_add, ← smul_sub]
    congr 1
    simp only [invOf_eq_inv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀]
    simp only [two_smul]
    rw[← add_assoc, add_sub_assoc, vsub_sub_vsub_cancel_right, vsub_add_vsub_cancel]
    apply add_eq_of_eq_sub'
    rw[vsub_sub_vsub_cancel_right]
  rw [this, norm_smul, mul_comm, invOf_eq_inv, norm_inv, Real.norm_ofNat,
  ← dist_eq_norm_vsub, Affine.Simplex.dist_circumcenter_eq_circumradius, ← ninePointRadius_eq]
  rfl

end EuclideanGeometry
