import SymmetricSubgroupAsymptotics.ProductQuartetKernelChart
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNonzeroOddQuotientSocles

/-! Actual nonzero-odd A4/S4 quartet frames have whole quotient-socle
bound two. All original denominators remain literal. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
namespace QuartetKernel
variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

 theorem alternating_nonzero_quotientSocle
    (hO : oddKernel C.quartetLinearImage≠⊥)
    (heven : alternatingGroup (Fin 4)≤C.top.range)
    (N : Subgroup T) [N.Normal] : SocleNormalGeneratorBound (T ⧸ N) 2 := by
  have hodd : oddKernel (B C)≠⊥ := by rw [linearImage_eq C]; exact hO
  have ht : ∀ p : alternatingGroup (Fin 4),∃ b : B C,
      (b : BinaryPlaneAlternatingKernelPartition.Frame).right=p.val := by
    intro p
    exact top_lift C p.val (heven p.property)
  exact BinaryPlaneAlternatingNonzeroOddQuotientSocles.quotientSocle
    (B C) hodd ht (pi C) (pi_surjective C) (A C) (E C)
    (inclusion C) (inclusion_injective C) N

end QuartetKernel
end SymmetricSubgroupAsymptotics.ProductBlockFrame
