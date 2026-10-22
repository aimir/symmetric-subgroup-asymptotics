import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPositivePivot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCleanup

/-! Actual root words normalize every original nonzero singular vector
in B-rank at least two. No equality with a full orthogonal group or
abstract polar-space transitivity hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
variable (K : Type) [Field K]

theorem exists_normalize_singular (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 2) → K) (hv : v ≠ 0) (hs : (gram K (s + 2)).toBilin' v v = 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      (g.val : Mat K (s + 2)) *ᵥ v = Pi.single (pos (s + 2) 0) 1 := by
  obtain ⟨g0, hg0⟩ := exists_positive_pivot K s v hv hs
  let v0 := (g0.val : Mat K (s + 2)) *ᵥ v
  let j : Fin (s + 2) := ⟨1, by omega⟩
  have hj : (0 : Fin (s + 2)) ≠ j := by
    intro he
    have hh := congrArg Fin.val he
    change 0 = 1 at hh
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize 0 j hj
    (positivePart K (s + 2) v0) hg0
  change A.val *ᵥ positivePart K (s + 2) v0 = Pi.single 0 1 at hA
  let d := doubleIntoElementary K (s + 2) A
  let b := d * g0
  let w := (b.val : Mat K (s + 2)) *ᵥ v
  have hwp : positivePart K (s + 2) w = Pi.single 0 1 := by
    change positivePart K (s + 2)
      ((((doubleIntoElementary K (s + 2) A).val : Mat K (s + 2)) *
        (g0.val : Mat K (s + 2))) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, double_positivePart]
    exact hA
  have hws : (gram K (s + 2)).toBilin' w w = 0 :=
    (CFSGOrthogonalBUnipotent.natural_pairing_invariant h2 (s + 2) b v v).trans hs
  obtain ⟨c, hc⟩ := exists_normalize_positive K h2 (s + 1) w hwp hws
  refine ⟨c * b, ?_⟩
  change ((c.val : Mat K (s + 2)) * (b.val : Mat K (s + 2))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
