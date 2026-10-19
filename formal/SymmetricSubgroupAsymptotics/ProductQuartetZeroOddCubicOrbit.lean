import SymmetricSubgroupAsymptotics.ProductQuartetKernelChart
import SymmetricSubgroupAsymptotics.ProductQuartetCubicOrbitCover
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalGeometry
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.OddCubicSubgroupLift

/-! Lift the actual coarse three-cycle in the zero-odd/no-pair branch
through the actual binary translation kernel. Its original point action
has at most eight orbits, without independent local cubic lifts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingCentralizerCommutators (top)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
open QuartetKernel
local instance quartetZeroOddCubicPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {T : Subgroup (Equiv.Perm (Fin 16))}
  (C : ProductBlockFrame T (Fin 4) Plane)

private theorem cubic_even : cycle ∈ alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign cycle = 1
  decide +kernel
private theorem cubic_cube : cycle ^ 3 = 1 := by decide +kernel
private theorem cubic_ne_one : cycle ≠ 1 := by decide +kernel

/-- The subgroup acts on the actual original sixteen points. -/
theorem zeroOdd_exists_odd_subgroup_eight_orbits
    (hzero : oddKernel C.quartetLinearImage = ⊥)
    (heven : alternatingGroup (Fin 4) ≤ C.top.range)
    (hNoPair : ¬ Nonempty (BinaryPairFrame T (Fin 8))) :
    ∃ P : Subgroup T, IsPGroup 3 P ∧
      Nat.card (MulAction.orbitRel.Quotient P (Fin 16)) ≤ 8 := by
  have heven' : ∀ p : alternatingGroup (Fin 4), ∃ b : B C,
      (b : BinaryPlaneAlternatingKernelPartition.Frame).right = p.val := by
    intro p
    exact top_lift C p.val (heven p.property)
  have hzero' : oddKernel (B C) = ⊥ := by rw [linearImage_eq]; exact hzero
  have hinj := BinaryPlaneZeroOddOriginalGeometry.top_injective T (B C)
    C.affineCoordinates (pi C) (fun _ => rfl) C.affinePointChart
    C.affineCoordinates_action hzero' heven' hNoPair
  obtain ⟨a, ha⟩ := heven' ⟨cycle, cubic_even⟩
  have hap : a ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    change (a : BinaryPlaneAlternatingKernelPartition.Frame).right ^ 3 = 1
    rw [ha]
    exact cubic_cube)
  have han : a ≠ 1 := by
    intro h
    have hh : cycle = 1 := ha.symm.trans (by rw [h]; rfl)
    exact cubic_ne_one hh
  let O : Subgroup (B C) := Subgroup.zpowers a
  have hocard : Nat.card O = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hap han]
  have ho : IsPGroup 3 O := IsPGroup.of_card (n := 1) (by simpa using hocard)
  have hocubic (o : O) : o ^ 3 = 1 := by
    simpa only [hocard] using (pow_card_eq_one' (x := o))
  obtain ⟨P,hP,_hle,hmap,_hcubic⟩ := OddCubicSubgroupLift.exists_lift
    (pi C) (pi_surjective C) ((E C).kernel_isPGroup_two (pi C) (A C)) O ho hocubic
  have haP : a ∈ P.map (pi C) := by
    rw [hmap]
    exact Subgroup.mem_zpowers a
  obtain ⟨g,hg,hga⟩ := haP
  have ht : C.top g = cycle := by
    have hh := congrArg (fun b : B C =>
      (b : BinaryPlaneAlternatingKernelPartition.Frame).right) hga
    change C.top g = (a : BinaryPlaneAlternatingKernelPartition.Frame).right at hh
    exact hh.trans ha
  exact ⟨P,hP,C.cubic_subgroup_orbit_card_le_eight P ⟨g,hg⟩ ht⟩

end SymmetricSubgroupAsymptotics.ProductBlockFrame
