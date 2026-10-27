import SymmetricSubgroupAsymptotics.FiniteExtensionFullImageRestrictedKernelCount
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-! Count all complete full-top lifts using only a binary bound on the
kernel and a genuine top tuple. No order bound on the top is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteExtensionFullTopBinaryKernelCount
local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
variable {E Q : Type} [Group E] [Group Q] [Finite E]

private def kernelCode (pi : E →* Q)
    (K : FiniteExtensionRestrictedKernelCount.KernelFamily pi (fun _ => True)) :
    Subgroup pi.ker := K.val.subgroupOf pi.ker

private theorem kernelCode_injective (pi : E →* Q) : Function.Injective (kernelCode pi) := by
  intro K M h
  have hm := congrArg (fun U : Subgroup pi.ker => U.map pi.ker.subtype) h
  apply Subtype.ext
  simpa only [kernelCode,Subgroup.map_subgroupOf_eq_of_le K.property.1,
    Subgroup.map_subgroupOf_eq_of_le M.property.1] using hm

theorem card_fullImage_le (pi : E →* Q) (hpi : Function.Surjective pi)
    (b : ℕ) (hb : Nat.card pi.ker≤2^b) {d : ℕ}
    (f : Fin d → Q) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (FiniteExtensionFullImageRestrictedKernelCount.Family pi (fun _ => True))≤
      2^(b*b)*(Nat.card pi.ker)^d := by
  have hk := (Nat.card_le_card_of_injective (kernelCode pi) (kernelCode_injective pi)).trans
    (subgroup_card_le_two_pow_sq b hb)
  exact (FiniteExtensionFullImageRestrictedKernelCount.card_family_le
    pi (fun _ => True) hpi f hf).trans (Nat.mul_le_mul_right _ hk)

end SymmetricSubgroupAsymptotics.FiniteExtensionFullTopBinaryKernelCount
