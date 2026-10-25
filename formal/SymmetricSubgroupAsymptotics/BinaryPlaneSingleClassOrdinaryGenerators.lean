import SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassSignDescent
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! In the actual single odd-kernel class, the whole actual top kernel
embeds in one GL2(F2) coordinate. Its ordinary rank is at most two, so the
native linear image costs at most two generators above its actual top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleClassOrdinaryGenerators
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] (C : Subgroup (W (R := R) (I := I)))

theorem genRank_le_top_add_two
    (htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp C.subtype))
    (i₀ : I) (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hlocal : ∃ u : oddKernel C, localLinear C i₀ u ≠ 1) :
    MarkedC4.genRank C ≤ MarkedC4.genRank R + 2 := by
  let pi : C →* R := PermutationalWreathProduct.rightHom.comp C.subtype
  let f : pi.ker →* Equiv.Perm (Fin 3) := toThree.comp
    (BinaryPlaneKernelClassSignDescent.topKernelLocal C i₀)
  have hf : Function.Injective f := toThree_injective.comp
    (BinaryPlaneKernelClassSignDescent.topKernelLocal_injective_of_single_class C i₀ hsingle hlocal)
  have hcard : Nat.card pi.ker ≤ 6 := by
    have hh := Nat.card_le_card_of_injective f hf
    have hs : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    exact hh.trans_eq hs
  have hk : MarkedC4.genRank pi.ker ≤ 2 := by
    have hp := FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card pi.ker
    by_contra hh
    have hge : 3 ≤ MarkedC4.genRank pi.ker := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hge
    norm_num at hpow
    omega
  have hq : MarkedC4.genRank (C ⧸ pi.ker) = MarkedC4.genRank R :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective pi htop)
  have hh := MarkedC4.genRank_le_of_normal pi.ker
  omega

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleClassOrdinaryGenerators
