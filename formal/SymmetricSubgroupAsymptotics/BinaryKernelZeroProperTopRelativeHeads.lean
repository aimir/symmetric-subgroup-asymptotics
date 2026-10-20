import SymmetricSubgroupAsymptotics.RelativeHeadAbelianSupplementCyclicCoverCompatible
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelZeroProperTopRelativeHeads
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G B C D : Type} [Group G] [Finite G] [Group B] [Finite B]
    [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (hproper : ∀ (L : Subgroup B) [L.Normal],L≠⊤ →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤0)
    (pi : G →* B) (hpi : Function.Surjective pi)
    (hK : IsMulCommutative pi.ker)
    (hkernel : ∀ (L : Subgroup G) [L.Normal], L≤pi.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤2)
    (cover : C × D →* G ⧸ commutator G) (hcover : Function.Surjective cover)

include hproper hpi hK hkernel hcover in
theorem relative_head_le_two (M : Subgroup G) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤2 := by
  let I := M.map pi
  letI : I.Normal := Subgroup.Normal.map inferInstance pi hpi
  by_cases hfull : I=⊤
  · have hsup : pi.ker ⊔ M=⊤ := by
      have h := congrArg (Subgroup.comap pi) hfull
      simpa only [I,Subgroup.comap_map_eq,Subgroup.comap_top,sup_comm] using h
    exact relativeHead_le_two_of_abelianSupplement_cyclicCover_compatible 2 cover hcover pi.ker M hsup hK
  · let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
    have he : (normalChainQuotient pi.ker M).map e.toMonoidHom=I := by
      change (M.map (QuotientGroup.mk' pi.ker)).map e.toMonoidHom=M.map pi
      rw [Subgroup.map_map]
      rfl
    have hi : Module.finrank (ZMod 2)
        (primeRelativeCharacters 2 (normalChainQuotient pi.ker M))≤0 :=
      (relativeCharacterAmbientCongr 2 e (normalChainQuotient pi.ker M) I he).finrank_eq.symm.le.trans
        (hproper I hfull)
    have hc := primeRelativeHead_chain_le (M ⊓ pi.ker) M 2 inf_le_left
    rw [primeRelativeHead_second_isomorphism 2 M pi.ker] at hc
    exact hc.trans (by have hk := hkernel (M ⊓ pi.ker) inf_le_right; omega)


end SymmetricSubgroupAsymptotics.BinaryKernelZeroProperTopRelativeHeads
