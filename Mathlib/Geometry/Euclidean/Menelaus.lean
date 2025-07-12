import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Angle.Sphere

open Module Affine Simplex EuclideanGeometry Real


namespace Affine
variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P] [DivisionRing k]


def ratioMap (A B : P) (q : k) [NeZero (1 + q)] : P :=
  AffineMap.lineMap A B (q / (1 + q))

@[simp]
theorem ratioMap_eq_lineMap (A B : P) (q : k) [NeZero (1 + q)] :
  ratioMap A B q = AffineMap.lineMap A B (q / (1 + q)) :=
  rfl



@[simp]
theorem ratioMap_same (A : P) (q : k) [NeZero (1 + q)] :
  ratioMap A A q = A := by
  dsimp [ratioMap]; simp


theorem meneluas_affine [Module k V] {A B C D E F : P} {k₁ k₂ k₃ : k}
  [NeZero (1 + k₁)] [NeZero (1 + k₂)] [NeZero (1 + k₃)]
    (hindep: AffineIndependent k ![A, B, C])
    (hD : D = ratioMap A B k₁)
    (hE : E = ratioMap B C k₂)
    (hF : F = ratioMap C A k₃) :
  Collinear k {D, E, F} ↔ k₁ * k₂ * k₃ = 1 := by

  set s := ({D, E, F}: Set P)
  have hd' : D ∈ s := by
    unfold s; simp;
  rw [collinear_iff_of_mem hd']
  constructor
  · sorry
  · intro h
    set hv := E -ᵥ D
    use hv
    rintro ⟨x, y, z⟩






end Affine
