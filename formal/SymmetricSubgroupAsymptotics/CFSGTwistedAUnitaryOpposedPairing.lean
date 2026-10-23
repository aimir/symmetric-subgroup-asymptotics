import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPoints

/-! The two literal singular coordinate halves pair nondegenerately.
Both implications use actual coordinate vectors and the signed form,
including characteristic two and a possible unused middle coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices

theorem unitaryStandard_single_mem (q : CFSG.PrimePower) (r : ℕ)
    (i : Fin (r + 1)) (hi : 2 * i.val + 1 ≤ r) :
    Pi.single i (1 : q.Extension 2) ∈ unitaryStandardSingularSpace q r := by
  intro j hj
  have hn : j ≠ i := by intro h; subst j; omega
  simp only [Pi.single_apply, if_neg hn]

theorem unitaryOpposite_single_mem (q : CFSG.PrimePower) (r : ℕ)
    (i : Fin (r + 1)) (hi : 2 * i.rev.val + 1 ≤ r) :
    Pi.single i (1 : q.Extension 2) ∈ unitaryOppositeSingularSpace q r := by
  rw [unitaryOppositeSingularSpace_mem_iff]
  intro j hj
  have hn : j ≠ i := by intro h; subst j; omega
  simp only [Pi.single_apply, if_neg hn]

theorem unitaryOpposite_pair_standard_nondegenerate (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) (hx : x ∈ unitaryOppositeSingularSpace q r)
    (hzero : ∀ y ∈ unitaryStandardSingularSpace q r, unitaryNaturalPair q r x y = 0) :
    x = 0 := by
  funext i
  by_cases hi : r < 2 * i.rev.val + 1
  · exact (unitaryOppositeSingularSpace_mem_iff q r x).mp hx i hi
  · have hp := hzero (Pi.single i.rev 1) (unitaryStandard_single_mem q r i.rev (by omega))
    have hs := (unitaryNaturalPair_zero_swap q r x (Pi.single i.rev 1)).mp hp
    rw [unitaryNaturalPair_basis, Fin.rev_rev] at hs
    exact (mul_eq_zero.mp hs).resolve_left (signWeight_ne_zero (q.Extension 2) r i.rev)

theorem unitaryStandard_pair_opposite_nondegenerate (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) (hx : x ∈ unitaryStandardSingularSpace q r)
    (hzero : ∀ y ∈ unitaryOppositeSingularSpace q r, unitaryNaturalPair q r x y = 0) :
    x = 0 := by
  funext i
  by_cases hi : r < 2 * i.val + 1
  · exact hx i hi
  · have hm : Pi.single i.rev (1 : q.Extension 2) ∈ unitaryOppositeSingularSpace q r :=
      unitaryOpposite_single_mem q r i.rev (by simpa only [Fin.rev_rev] using Nat.le_of_not_gt hi)
    have hp := hzero (Pi.single i.rev 1) hm
    have hs := (unitaryNaturalPair_zero_swap q r x (Pi.single i.rev 1)).mp hp
    rw [unitaryNaturalPair_basis, Fin.rev_rev] at hs
    exact (mul_eq_zero.mp hs).resolve_left (signWeight_ne_zero (q.Extension 2) r i.rev)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
