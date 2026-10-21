import SymmetricSubgroupAsymptotics.PGroupPermutationPointwiseAnnihilator
import SymmetricSubgroupAsymptotics.PermutationBinarySmallDenominatorFaithful
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! The preimage of an actual invariant interval T>A has trivial
pointwise stabilizer modulo the original lower denominator A. The lower
full layer first kills the actual base permutation; the retained kernel
then acts by POINTWISE multiplication, whose invariant annihilator is zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance intervalKernelStabilizerPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem eq_one_of_interval_preimage_displacement
    (hU : IsPGroup 2 U) (i : Fin w)
    (A T : Subrepresentation (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)))
    (hsmall : 2*Module.finrank (ZMod 2) A.toSubmodule < w)
    (hnot : ¬T.toSubmodule ≤ A.toSubmodule)
    (u : U)
    (hdisplacement : ∀ v : X → ZMod 2,F.pairSum v ∈ T.toSubmodule →
      permutationFunctionRepresentation (ZMod 2) U X u v-v ∈ A.toSubmodule.map F.pairConstant) :
    u=1 := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  have ht : F.top.rangeRestrict u=1 := by
    apply binary_permutation_eq_one_of_small_denominator (F.top_isPGroup hU) i A
      (by simpa only [Nat.card_fin] using hsmall)
    intro a
    have hm := hdisplacement (F.pairConstant a) (by
      rw [F.pairSum_pairConstant]
      exact T.toSubmodule.zero_mem)
    have he : permutationFunctionRepresentation (ZMod 2) U X u (F.pairConstant a)-
        F.pairConstant a = F.pairConstant
          (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin w)
            (F.top.rangeRestrict u) a-a) := by
      rw [F.pairConstant_action,map_sub]
      rfl
    rw [he] at hm
    obtain ⟨b,hb,heq⟩ := hm
    have heq' := F.pairConstant_injective heq
    exact heq' ▸ hb
  have hu : u ∈ F.top.ker := congrArg Subtype.val ht
  let k : F.top.ker := ⟨u,hu⟩
  have hbits : F.bits k ∈ (permutationPointwiseAnnihilator A T).toSubmodule := by
    intro a ha
    have hm := hdisplacement (F.pairSumSection a) (by rwa [F.pairSum_pairSumSection])
    change permutationFunctionRepresentation (ZMod 2) U X k.val (F.pairSumSection a)-
      F.pairSumSection a ∈ A.toSubmodule.map F.pairConstant at hm
    rw [F.kernel_displacement_eq_pairConstant_product,F.pairSum_pairSumSection] at hm
    obtain ⟨b,hb,he⟩ := hm
    exact (F.pairConstant_injective he) ▸ hb
  rw [permutationPointwiseAnnihilator_eq_bot_of_not_le (F.top_isPGroup hU) i A T hnot] at hbits
  have hk : k=1 := by
    apply F.bitsHom_injective
    rw [map_one]
    exact congrArg Multiplicative.ofAdd (show F.bits k=0 from hbits)
  exact congrArg Subtype.val hk

end SymmetricSubgroupAsymptotics.BinaryPairFrame
