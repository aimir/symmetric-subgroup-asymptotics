import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalHom
import SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalHom

/-! The actual odd-B tail embedding normalizes the actual whole point
radical. Its action on the parameter is exactly its original natural
tail action, including the middle coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalNormalizer

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPointRadicalHom
open CFSGOrthogonalBOddPoleShearElementary CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBOddPoleCoordinates CFSGOrthogonalBOddPoleShear
open CFSGOrthogonalBOddQuadraticForm
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem tail_coordinates (s : ℕ) (g : elementaryRootGroup K (s + 2))
    (v : Index (s + 3) → K) :
    coordinates K (s + 2)
      (((tailElementaryHom K (s + 2) g).val : Mat K (s + 3)) *ᵥ v) =
      QuadraticHyperbolicRadicalHom.levi (naturalLinearHom K (s + 2) g)
        (coordinates K (s + 2) v) := by
  apply Prod.ext
  · exact tailElementaryHom_head_positive K (s + 2) g v
  · apply Prod.ext
    · exact tailElementaryHom_tail_action K (s + 2) g v
    · change 2 * (((tailElementaryHom K (s + 2) g).val : Mat K (s + 3)) *ᵥ v)
        (neg (s + 3) 0) = 2 * v (neg (s + 3) 0)
      rw [tailElementaryHom_head_negative]

omit [Finite K] in
theorem tail_preserves_quadratic (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 2)) (z : Index (s + 2) → K) :
    quadratic K (s + 2) (naturalLinearHom K (s + 2) g z) =
      quadratic K (s + 2) z := elementary_preserves_quadratic K h2 (s + 2) g z

omit [Finite K] in
theorem tail_radical_intertwine (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 2)) (z : Index (s + 2) → K)
    (v : Index (s + 3) → K) :
    ((tailElementaryHom K (s + 2) g).val : Mat K (s + 3)) *ᵥ
        poleShear K h2 (s + 2) z v =
      poleShear K h2 (s + 2) (naturalLinearHom K (s + 2) g z)
        (((tailElementaryHom K (s + 2) g).val : Mat K (s + 3)) *ᵥ v) := by
  apply (coordinateEquiv K h2 (s + 2)).injective
  change coordinates K (s + 2) _ = coordinates K (s + 2) _
  rw [tail_coordinates, coordinates_poleShear, coordinates_poleShear, tail_coordinates]
  exact QuadraticHyperbolicRadicalHom.levi_transform
    (quadratic K (s + 2)) (naturalLinearHom K (s + 2) g)
    (tail_preserves_quadratic K h2 s g) z (coordinates K (s + 2) v)

theorem tail_radical_commutation (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 2)) (z : Index (s + 2) → K) :
    tailElementaryHom K (s + 2) g * radicalHom K h2 s (Multiplicative.ofAdd z) =
      radicalHom K h2 s (Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z)) *
        tailElementaryHom K (s + 2) g := by
  have he : ∀ v : Index (s + 3) → K,
      (((tailElementaryHom K (s + 2) g).val : Mat K (s + 3)) *
        ((radicalHom K h2 s (Multiplicative.ofAdd z)).val : Mat K (s + 3))) *ᵥ v =
      (((radicalHom K h2 s (Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z))).val :
        Mat K (s + 3)) * ((tailElementaryHom K (s + 2) g).val : Mat K (s + 3))) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      radicalHom_apply, radicalHom_apply]
    exact tail_radical_intertwine K h2 s g z v
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hh := congrFun (he (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh

theorem radical_tail_conjugation (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 2)) (z : Index (s + 2) → K) :
    radicalHom K h2 s (Multiplicative.ofAdd (naturalLinearHom K (s + 2) g z)) =
      tailElementaryHom K (s + 2) g * radicalHom K h2 s (Multiplicative.ofAdd z) *
        (tailElementaryHom K (s + 2) g)⁻¹ := by
  have hh := congrArg (fun x : elementaryRootGroup K (s + 3) =>
    x * (tailElementaryHom K (s + 2) g)⁻¹) (tail_radical_commutation K h2 s g z)
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalNormalizer
