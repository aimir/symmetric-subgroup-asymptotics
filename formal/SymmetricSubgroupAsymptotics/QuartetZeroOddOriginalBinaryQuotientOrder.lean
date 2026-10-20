import SymmetricSubgroupAsymptotics.ProductQuartetZeroOddQuotientBounds
import SymmetricSubgroupAsymptotics.ProductQuartetZeroOddCubicOrbit
import SymmetricSubgroupAsymptotics.BinaryPairOddOrbitSectionBound

/-! The zero-odd/no-pair quartet branch gives binary original quotients
of order at most 2^11. Both factors are attached to the SAME original N. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open OriginalKernelModuleChart
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 16))
  (C : ProductBlockFrame F.top.range (Fin 4) Plane)

/-- The actual odd subgroup pays eight kernel coordinates, while the
retained quotient of the actual sixteen-point top has order at most eight. -/
theorem zeroOdd_binary_quotient_card_le_eleven
    (hzero : oddKernel C.quartetLinearImage = ⊥)
    (heven : alternatingGroup (Fin 4) ≤ C.top.range)
    (hNoPair : ¬ Nonempty (BinaryPairFrame F.top.range (Fin 8)))
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    Nat.card (U ⧸ N) ≤ 2 ^ 11 := by
  obtain ⟨P,hP,horbits⟩ := C.zeroOdd_exists_odd_subgroup_eight_orbits hzero heven hNoPair
  let pi := F.top.rangeRestrict
  let R := U ⧸ (pi.ker ⊔ N)
  let phi := sectionTop pi N F.top.rangeRestrict_surjective
  have hphi : Function.Surjective phi := by
    intro r
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) r
    exact ⟨pi u,(sectionTop_apply pi N F.top.rangeRestrict_surjective u).trans hu⟩
  have hR : IsPGroup 2 R := hQ.of_surjective (base pi N) (base_surjective pi N)
  have hresidual : Nat.card R ≤ 2 ^ 3 := by
    simpa only [show (2 : ℕ)^3 = 8 from rfl] using
      C.zeroOdd_binary_image_card_le_eight hzero heven hNoPair phi hphi hR
  exact F.binary_quotient_card_le_of_odd_orbits P hP 8 3 horbits N hQ hresidual

end SymmetricSubgroupAsymptotics.BinaryPairFrame
