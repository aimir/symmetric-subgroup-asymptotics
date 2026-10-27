import SymmetricSubgroupAsymptotics.FiniteAbelianExtensionWholeLayerCount
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation

/-! Literal invariant-kernel and ALL-lift count in an original elementary
module extension. The normality is in the WHOLE extension group. The
existing chart binds the quotient action and retains each actual kernel.
No splitting or unknown subgroup-count bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalKernelWholeLayerCount
open FiniteAbelianExtensionWholeLayerCount

variable {p : ℕ} [Fact p.Prime] {E Q : Type} [Group E] [Finite E] [Group Q]
    (π : E →* Q) (hπ : Function.Surjective π)
    (A : Rep (ZMod p) Q) (chart : OriginalKernelModuleChart π A)

include π hπ A chart

private def kernelCode (K : InvariantKernel π) : Subrepresentation A.ρ := by
  letI : K.val.Normal := K.property.2
  exact chart.normalSubrepresentation π hπ A K.val

private theorem kernelCode_injective : Function.Injective (kernelCode π hπ A chart) := by
  intro K M h
  letI : K.val.Normal := K.property.2
  letI : M.val.Normal := M.property.2
  change chart.normalSubrepresentation π hπ A K.val=
    chart.normalSubrepresentation π hπ A M.val at h
  have hi := (chart.normalSubrepresentation_eq_iff_intersection_eq π hπ A K.val M.val).mp h
  have hm := congrArg (fun U : Subgroup π.ker => U.map π.ker.subtype) hi
  apply Subtype.ext
  simpa only [Subgroup.subgroupOf_map_subtype,inf_eq_left.mpr K.property.1,
    inf_eq_left.mpr M.property.1] using hm

theorem card_invariantKernel_le_subrepresentation :
    Nat.card (InvariantKernel π) ≤ Nat.card (Subrepresentation A.ρ) := by
  letI : Finite A := Finite.of_equiv π.ker chart.equiv.symm.toEquiv
  exact Nat.card_le_card_of_injective (kernelCode π hπ A chart)
    (kernelCode_injective π hπ A chart)

theorem kernel_commutative : IsMulCommutative π.ker := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply chart.equiv.symm.injective
  simpa only [map_mul] using (mul_comm (chart.equiv.symm x) (chart.equiv.symm y))

theorem card_fullImage_le_subrepresentation {d : ℕ} (f : Fin d → Q)
    (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (FullImage π) ≤ Nat.card (Subrepresentation A.ρ)*(Nat.card π.ker)^d :=
  (FiniteAbelianExtensionWholeLayerCount.card_fullImage_le π hπ
    (kernel_commutative π hπ A chart) f hf).trans
      (Nat.mul_le_mul_right _ (card_invariantKernel_le_subrepresentation π hπ A chart))

/-- Actual uniform module generators and actual quotient generators count
all elementary-layer subgroups, including every nonsplit lift. -/
theorem card_fullImage_le_of_uniform {H d : ℕ}
    (hgen : UniformSubrepresentationGeneratorBound A.ρ H)
    (f : Fin d → Q) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (FullImage π) ≤ (Nat.card A)^(H+d) := by
  letI : Finite A := Finite.of_equiv π.ker chart.equiv.symm.toEquiv
  have hc : Nat.card π.ker=Nat.card A := Nat.card_congr chart.equiv.symm.toEquiv
  have hh := (card_fullImage_le_subrepresentation π hπ A chart f hf).trans
    (Nat.mul_le_mul_right _ hgen.card_subrepresentation_le)
  simpa only [hc,pow_add] using hh

end SymmetricSubgroupAsymptotics.OriginalKernelWholeLayerCount
