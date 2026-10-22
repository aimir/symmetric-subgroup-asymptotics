import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNegativeShortAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBClearNegativeShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularRootPlanes

/-! Once the original positive vector is e0, actual negative short and
alternating shear words normalize the whole singular B-vector. The
original Gram equation supplies the paired negative coordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

theorem exists_normalize_positive (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 1) → K) (hp : positivePart K (s + 1) v = Pi.single 0 1)
    (hs : (gram K (s + 1)).toBilin' v v = 0) :
    ∃ g : elementaryRootGroup K (s + 1),
      (g.val : Mat K (s + 1)) *ᵥ v = Pi.single (pos (s + 1) 0) 1 := by
  let d := negativeShortElement K s 0 (v (middle (s + 1)) / 2)
  let w := (d.val : Mat K (s + 1)) *ᵥ v
  obtain ⟨hwp, hwm⟩ := negativeShort_kills_middle K h2 s v hp
  change positivePart K (s + 1) w = Pi.single 0 1 at hwp
  change w (middle (s + 1)) = 0 at hwm
  have hws : (gram K (s + 1)).toBilin' w w = 0 :=
    (CFSGOrthogonalBUnipotent.natural_pairing_invariant h2 (s + 1) d v v).trans hs
  have hn := gram_norm_positive_basis K s w hwp
  have hny : (4 : K) * w (neg (s + 1) 0) = 0 := by
    simpa only [hwm, zero_pow (by decide : 2 ≠ 0), add_zero] using hn.symm.trans hws
  have h4 : (4 : K) ≠ 0 := by
    have hh : (4 : K) = 2 * 2 := by ring
    rw [hh]
    exact mul_ne_zero h2 h2
  have hy := (mul_eq_zero.mp hny).resolve_left h4
  let c := clearNegativeElement K h2 s (negativePart K (s + 1) w)
  have hc : (c.val : Mat K (s + 1)) *ᵥ w = Pi.single (pos (s + 1) 0) 1 :=
    clearNegativeElement_action K h2 s w hwp hy hwm
  refine ⟨c * d, ?_⟩
  change ((c.val : Mat K (s + 1)) * (d.val : Mat K (s + 1))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
