import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPairRootRealization

/-! A singular-parameter full odd-B pole shear is exactly one minus
the literal Gram pair operator of the first pole and the actual tail
vector. The sign and the normalized opposite coordinate are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPolePairOperator

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBOddQuadraticForm CFSGOrthogonalBOddPoleCoordinates
open CFSGOrthogonalBOddPoleShear CFSGQuadraticHyperbolicShear CFSGAlternatingPairOperator
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem coordinates_first (n : ℕ) :
    coordinates K n (Pi.single (pos (n + 1) 0) 1) = (1, (0, 0)) := by
  apply Prod.ext
  · simp [coordinates]
  · apply Prod.ext
    · funext i
      rcases i with (i | i) | ⟨⟩ <;>
        simp [coordinates, tailRestriction, tailIndex, pos, neg, middle]
    · simp [coordinates, pos, neg]

omit [Finite K] in
theorem coordinates_tailExtension (n : ℕ) (z : Index n → K) :
    coordinates K n (tailExtension K n z) = (0, (z, 0)) := by
  apply Prod.ext
  · exact tailExtension_positive_head K n z
  · apply Prod.ext
    · exact tailRestriction_extension K n z
    · change 2 * tailExtension K n z (neg (n + 1) 0) = 0
      rw [tailExtension_negative_head, mul_zero]

omit [Finite K] in
theorem polar_coordinates (h2 : (2 : K) ≠ 0) (n : ℕ)
    (v w : Index (n + 1) → K) :
    (quadratic K (n + 1)).polarBilin v w =
      (coordinates K n v).1 * (coordinates K n w).2.2 +
      (coordinates K n w).1 * (coordinates K n v).2.2 +
      (quadratic K n).polarBilin (coordinates K n v).2.1 (coordinates K n w).2.1 := by
  let E := coordinateEquiv K h2 n
  change quadratic K (n + 1) (v + w) - quadratic K (n + 1) v -
    quadratic K (n + 1) w = _
  rw [quadratic_coordinates K h2 n, quadratic_coordinates K h2 n, quadratic_coordinates K h2 n]
  change norm (quadratic K n) (E (v + w)) - norm (quadratic K n) (E v) -
    norm (quadratic K n) (E w) = _
  rw [map_add]
  change ((E v).1 + (E w).1) * ((E v).2.2 + (E w).2.2) +
      quadratic K n ((E v).2.1 + (E w).2.1) -
      ((E v).1 * (E v).2.2 + quadratic K n (E v).2.1) -
      ((E w).1 * (E w).2.2 + quadratic K n (E w).2.1) =
    (E v).1 * (E w).2.2 + (E w).1 * (E v).2.2 +
      (quadratic K n ((E v).2.1 + (E w).2.1) -
        quadratic K n (E v).2.1 - quadratic K n (E w).2.1)
  ring

theorem poleShear_singular_pairOperator (h2 : (2 : K) ≠ 0) (n : ℕ)
    (z : Index n → K) (hz : quadratic K n z = 0) (v : Index (n + 1) → K) :
    poleShear K h2 n z v = v -
      pairOperator (gram K (n + 1)).toBilin' (Pi.single (pos (n + 1) 0) 1)
        (tailExtension K n z) v := by
  have hp : (gram K (n + 1)).toBilin' (Pi.single (pos (n + 1) 0) 1) v =
      (coordinates K n v).2.2 := by
    rw [← quadratic_polar K h2 (n + 1), polar_coordinates K h2 n, coordinates_first]
    simp
  have ht : (gram K (n + 1)).toBilin' (tailExtension K n z) v =
      (quadratic K n).polarBilin z (coordinates K n v).2.1 := by
    rw [← quadratic_polar K h2 (n + 1), polar_coordinates K h2 n, coordinates_tailExtension]
    simp
  apply (coordinateEquiv K h2 n).injective
  change coordinates K n (poleShear K h2 n z v) =
    coordinateEquiv K h2 n (v - pairOperator (gram K (n + 1)).toBilin'
      (Pi.single (pos (n + 1) 0) 1) (tailExtension K n z) v)
  rw [coordinates_poleShear, map_sub, pairOperator_apply, map_sub, map_smul, map_smul]
  change transform (quadratic K n) z (coordinates K n v) = coordinates K n v -
    ((gram K (n + 1)).toBilin' (tailExtension K n z) v •
      coordinates K n (Pi.single (pos (n + 1) 0) 1) -
      (gram K (n + 1)).toBilin' (Pi.single (pos (n + 1) 0) 1) v •
        coordinates K n (tailExtension K n z))
  rw [hp, ht, coordinates_first, coordinates_tailExtension]
  generalize coordinates K n v = x
  rcases x with ⟨a, w, b⟩
  apply Prod.ext
  · change a - QuadraticMap.polar (quadratic K n) z w - quadratic K n z * b =
      a - ((quadratic K n).polarBilin z w * 1 - b * 0)
    rw [hz, QuadraticMap.polarBilin_apply_apply]
    ring
  · apply Prod.ext
    · change w + b • z = w - ((quadratic K n).polarBilin z w • (0 : Index n → K) - b • z)
      module
    · change b = b - ((quadratic K n).polarBilin z w * 0 - b * 0)
      ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPolePairOperator
