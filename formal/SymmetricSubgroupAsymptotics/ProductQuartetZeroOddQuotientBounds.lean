import SymmetricSubgroupAsymptotics.ProductQuartetKernelChart
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalNonbinarySocles
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddOriginalBinaryQuotient

/-! Bind the checked zero-odd/no-pair quartet quotient theorems to an
actual physical quartet frame. No finite row, capacity or source premise
is retained. Every denominator is the original subgroup denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open QuartetKernel
variable {T : Subgroup (Equiv.Perm (Fin 16))}
  (C : ProductBlockFrame T (Fin 4) Plane)
  (hzero : oddKernel C.quartetLinearImage = ⊥)
  (heven : alternatingGroup (Fin 4) ≤ C.top.range)
  (hNoPair : ¬ Nonempty (BinaryPairFrame T (Fin 8)))

include heven in
private theorem kernel_heven : ∀ p : alternatingGroup (Fin 4),
    ∃ h : B C, (h : BinaryPlaneAlternatingKernelPartition.Frame).right = p.val := by
  intro p
  exact top_lift C p.val (heven p.property)

include hzero in
private theorem kernel_zero : oddKernel (B C) = ⊥ := by
  rw [linearImage_eq]
  exact hzero

include hzero heven hNoPair

/-- Every nonbinary quotient of this actual sixteen-point top has socle
normal-generation bound two. -/
theorem zeroOdd_nonbinary_quotient_socle_two
    (N : Subgroup T) [N.Normal] (hQ : ¬ IsPGroup 2 (T ⧸ N)) :
    SocleNormalGeneratorBound (T ⧸ N) 2 := by
  exact BinaryPlaneZeroOddOriginalNonbinarySocles.socle_bound T (B C)
    C.affineCoordinates (pi C) (pi_surjective C) (fun _ => rfl)
    C.affinePointChart C.affineCoordinates_action
    (kernel_zero C hzero) (kernel_heven C heven) hNoPair
    (A C) (E C) (inclusion C) (inclusion_injective C) N hQ

/-- Binary quotients of the same original top have order at most eight. -/
theorem zeroOdd_binary_quotient_card_le_eight
    (N : Subgroup T) [N.Normal] (hQ : IsPGroup 2 (T ⧸ N)) :
    Nat.card (T ⧸ N) ≤ 8 := by
  exact BinaryPlaneZeroOddOriginalBinaryQuotient.quotient_card_le_eight T (B C)
    C.affineCoordinates (pi C) (pi_surjective C) (fun _ => rfl)
    C.affinePointChart C.affineCoordinates_action
    (kernel_zero C hzero) (kernel_heven C heven) hNoPair
    (A C) (E C) (inclusion C) (inclusion_injective C) N hQ

/-- The target is allowed to be the retained top of any original normal
axis in a larger binary extension. -/
theorem zeroOdd_binary_image_card_le_eight
    {R : Type} [Group R] [Finite R] (f : T →* R)
    (hf : Function.Surjective f) (hR : IsPGroup 2 R) : Nat.card R ≤ 8 := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hQ : IsPGroup 2 (T ⧸ f.ker) := hR.of_equiv e.symm
  have hh := C.zeroOdd_binary_quotient_card_le_eight hzero heven hNoPair f.ker hQ
  rw [Nat.card_congr e.toEquiv] at hh
  exact hh

end SymmetricSubgroupAsymptotics.ProductBlockFrame
