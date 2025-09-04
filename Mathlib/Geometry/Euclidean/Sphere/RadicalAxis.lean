
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Sphere.Power

open Real

open RealInnerProductSpace Real
open EuclideanGeometry
open Affine Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]


noncomputable section


namespace EuclideanGeometry



def Sphere.CenterDist (s1 s2 : Sphere P) : ℝ :=
  dist s1.center s2.center

def Sphere.set (s : Sphere P) : Set P := {x | s.power x = 0  }

def Sphere.interior (s : Sphere P) : Set P := {x | s.power x < 0  }
def Sphere.exterior (s : Sphere P) : Set P := {x | s.power x > 0  }

def Sphere.inter (s1 s2 : Sphere P) : Set P := s1 ∩ s2


def Sphere.IsTangentSphere (s1 s2 : Sphere P) : Prop :=
  s1.IsIntTangent s2 ∨ s1.IsExtTangent s2


theorem Sphere.inter_card_eq_one_iff_isTangent {s1 s2 : Sphere P} :
    (s1.inter s2).ncard = 1 ↔ Sphere.IsTangentSphere s1 s2 := by
  sorry

-- need better definition
def Sphere.IsIntersection (s1 s2 : Sphere P) : Prop :=
  let d:= Sphere.CenterDist s1 s2
  let r1 := s1.radius
  let r2 := s2.radius
  d < r1 + r2 ∧ |r1 - r2| < d


def Sphere.InterSphereNonempty (s1 s2 : Sphere P) : Prop :=
  (s1.inter s2).Nonempty

theorem Sphere.inter_card_gt_one_iff_hasIntersection {s1 s2 : Sphere P} :
    (s1.inter s2).ncard > 1 ↔ Sphere.IsIntersection s1 s2 := by
  sorry

theorem Sphere.inter_nonempty_iff {s1 s2 : Sphere P} :
    (s1.inter s2).Nonempty ↔ Sphere.IsTangentSphere s1 s2 ∨ Sphere.IsIntersection s1 s2 := by
  sorry


def Sphere.CommonPoint (s1 s2 : Sphere P) (p : P) : Prop :=
  p ∈ s1 ∧ p ∈ s2


def Sphere.symmPointOnCenters (s1 s2 : Sphere P) {p : P} (h : Sphere.CommonPoint s1 s2 p) : P :=
  let line := affineSpan ℝ {s1.center, s2.center}
  have hs: line.direction.HasOrthogonalProjection :=by sorry
  reflection  (affineSpan  ℝ {s1.center, s2.center}) p

section RadicalAxis

def Sphere.radicalAxis (s1 s2 : Sphere P) : AffineSubspace ℝ P :=
  let ps := {x : P | s1.power x = s2.power x}
  AffineSubspace.mk (affineSpan ℝ ps) (by sorry)


theorem Sphere.radicalAxis_eq_top {s1 s2 : Sphere P} :
    (s1.radicalAxis s2) = ⊤ ↔ s1 = s2 := by
  sorry

theorem Sphere.radicalAxis_eq_empty {s1 s2 : Sphere P} :
    (s1.radicalAxis s2) = ⊥ ↔ s1.center = s2.center ∧ s1.radius ≠ s2.radius := by
  sorry


theorem Sphere.mem_radicalAxis_pow_eq {s1 s2 : Sphere P} {p : P} (hp : p ∈ s1.radicalAxis s2) :
    s1.power p = s2.power p := by
  sorry


end RadicalAxis

section DimensionTwo

variable [Fact (finrank ℝ V = 2)]


theorem Circle.inter_card_eq_two_iff (s1 s2 : Sphere P) :
    (s1.inter s2).ncard = 2 ↔ Sphere.IsIntersection s1 s2 := by
  sorry

theorem Circle.radicalAxis_eq_line {s1 s2 : Sphere P} {p : P} (hs : s1.IsIntersection s2)
  (hp : Sphere.CommonPoint s1 s2 p) :
    (s1.radicalAxis s2) = line[ℝ, p, s1.symmPointOnCenters s2 hp] := by
  sorry



end DimensionTwo

end EuclideanGeometry


end
