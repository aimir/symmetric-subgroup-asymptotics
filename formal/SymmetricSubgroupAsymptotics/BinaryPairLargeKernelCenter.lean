import SymmetricSubgroupAsymptotics.BinaryPairActualKernelDualSections
import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
import SymmetricSubgroupAsymptotics.OriginalKernelCenter

/-! Faithfulness of an actual kernel of dimension greater than half the
point degree puts the original centre inside that kernel. Under the
original transitive top action its bits are literally constant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance largeKernelCenterFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem original_center_le_kernel_of_half_lt
    [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U) (x : Fin w)
    (hlarge : w<2*Module.finrank (ZMod 2) F.kernelSpace) :
    Subgroup.center U≤F.top.ker := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  let M := F.kernelTopPermutationSubrepresentation
  let q : M.toRepresentation.IntertwiningMap M.toRepresentation :=
    Representation.IntertwiningMap.id _
  have hinj : Function.Injective M.toRepresentation :=
    permutationSection_injective_of_half_lt (F.top_isPGroup hU) x
      M.toRepresentation M q (fun v => ⟨v,rfl⟩) (by simpa using hlarge)
  intro z hz
  have he : F.top.rangeRestrict z=1 :=
    (F.actualOriginalKernelChart).center_le_ker hinj hz
  exact congrArg Subtype.val he

omit [Finite X] in
theorem central_kernel_bits_constant
    [MulAction.IsPretransitive F.top.range (Fin w)]
    (z : F.top.ker) (hz : (z : U)∈Subgroup.center U) (x y : Fin w) :
    F.bits z x=F.bits z y := by
  have hfix (t : F.top.range) : F.coordinateTopAction t (F.bits z)=F.bits z := by
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    rw [F.coordinateTopAction_bits]
    congr 1
    apply Subtype.ext
    change u*(z : U)*u⁻¹=(z : U)
    rw [Subgroup.mem_center_iff.mp hz u]
    simp only [mul_assoc,mul_inv_cancel,mul_one]
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq F.top.range x y
  have he := congrFun (hfix t) y
  change F.bits z (t.val.symm y)=F.bits z y at he
  have hi : t.val.symm y=x := by
    change t⁻¹ • y=x
    rw [←ht,inv_smul_smul]
  rwa [hi] at he

end SymmetricSubgroupAsymptotics.BinaryPairFrame
