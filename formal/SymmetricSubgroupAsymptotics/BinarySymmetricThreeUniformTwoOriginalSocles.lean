import SymmetricSubgroupAsymptotics.OriginalKernelUniformRelativeHead
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.NaturalThreeProperBinaryRelativeHead
import SymmetricSubgroupAsymptotics.BinaryKernelZeroProperTopRelativeHeads
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralOriginalQuotientSocles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySymmetricThreeUniformTwoOriginalSocles
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
 theorem quotientSocle {G X C D : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (hX : Nat.card X=12) (pi : G →* Equiv.Perm (Fin 3))
    (hpi : Function.Surjective pi) (A : Rep.{0} (ZMod 2) (Equiv.Perm (Fin 3)))
    [FiniteDimensional (ZMod 2) A] (E : OriginalKernelModuleChart pi A)
    (hu : UniformSubrepresentationGeneratorBound A.ρ 2)
    (cover : C × D →* G ⧸ commutator G) (hcover : Function.Surjective cover)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  have hK : IsMulCommutative pi.ker := IsMulCommutative.of_comm fun x y =>
    E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm])
  have hh := BinaryKernelZeroProperTopRelativeHeads.relative_head_le_two
    NaturalThreeProperBinaryRelativeHead.relative_head_zero pi hpi hK
    (E.relative_head_le_of_uniform pi A hpi 2 hu) cover hcover
  exact TwelvePointRemainingStructural.quotientSocle_two_of_original_symmetricThree
    (X:=X) hX pi hpi (E.kernel_isPGroup_two pi A) hh N
end SymmetricSubgroupAsymptotics.BinarySymmetricThreeUniformTwoOriginalSocles
