import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormPositivePivot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormCleanup

/-! Exact all-norm natural-vector transitivity by actual odd-B words,
uniformly from rank two. This retains the genuine low-tail case without
requiring a new maximal singular-pair frame. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormVectorOrbit

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBGenerationSLChain CFSGOrthogonalBOddQuadraticForm
open CFSGOrthogonalBAllNormCleanup
variable (K : Type) [Field K]

theorem exists_normalize_norm (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 2) → K) (hv : v ≠ 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      (g.val : Mat K (s + 2)) *ᵥ v =
        normRepresentative K (s + 1) (quadratic K (s + 2) v) := by
  obtain ⟨g0, hg0⟩ := CFSGOrthogonalBAllNormPositivePivot.exists_positive_pivot K s v hv
  let v0 := (g0.val : Mat K (s + 2)) *ᵥ v
  let j : Fin (s + 2) := ⟨1, by omega⟩
  have hj : (0 : Fin (s + 2)) ≠ j := by
    intro he
    have h := congrArg Fin.val he
    change 0 = 1 at h
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize 0 j hj
    (positivePart K (s + 2) v0) hg0
  change A.val *ᵥ positivePart K (s + 2) v0 = Pi.single 0 1 at hA
  let b := doubleIntoElementary K (s + 2) A * g0
  let w := (b.val : Mat K (s + 2)) *ᵥ v
  have hwp : positivePart K (s + 2) w = Pi.single 0 1 := by
    change positivePart K (s + 2)
      ((((doubleIntoElementary K (s + 2) A).val : Mat K (s + 2)) *
        (g0.val : Mat K (s + 2))) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, double_positivePart]
    exact hA
  obtain ⟨c, hc⟩ := CFSGOrthogonalBAllNormCleanup.exists_normalize_positive K h2 (s + 1) w hwp
  have hwQ : quadratic K (s + 2) w = quadratic K (s + 2) v :=
    elementary_preserves_quadratic K h2 (s + 2) b v
  rw [hwQ] at hc
  refine ⟨c * b, ?_⟩
  change ((c.val : Mat K (s + 2)) * (b.val : Mat K (s + 2))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hc

theorem exists_map_of_same_norm (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v w : Index (s + 2) → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (hQ : quadratic K (s + 2) v = quadratic K (s + 2) w) :
    ∃ g : elementaryRootGroup K (s + 2), (g.val : Mat K (s + 2)) *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_normalize_norm K h2 s v hv
  obtain ⟨b, hb⟩ := exists_normalize_norm K h2 s w hw
  have hbi : (↑(b.val⁻¹) : Mat K (s + 2)) *ᵥ
      normRepresentative K (s + 1) (quadratic K (s + 2) w) = w := by
    rw [← hb, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨b⁻¹ * a, ?_⟩
  change ((↑(b.val⁻¹) : Mat K (s + 2)) * (a.val : Mat K (s + 2))) *ᵥ v = w
  rw [← Matrix.mulVec_mulVec, ha, hQ, hbi]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormVectorOrbit
