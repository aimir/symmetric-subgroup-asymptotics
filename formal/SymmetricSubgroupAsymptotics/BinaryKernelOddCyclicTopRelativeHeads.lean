import SymmetricSubgroupAsymptotics.OddKernelCyclicUpperRelativeHead

/-! A normal binary-kernel head and an odd-by-cyclic actual top share
at most two relative-head positions for every original normal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelOddCyclicTopRelativeHeads
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem relative_head_le_two {G B R : Type} [Group G] [Finite G]
    [Group B] [Finite B] [Group R] [Finite R] [IsCyclic R]
    (pi : G →* B) (hpi : Function.Surjective pi)
    (beta : B →* R) (hbeta : Function.Surjective beta) (hodd : IsPGroup 3 beta.ker)
    (hkernel : ∀ (L : Subgroup G) [L.Normal], L≤pi.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤1)
    (M : Subgroup G) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤2 := by
  let I := M.map pi
  letI : I.Normal := Subgroup.Normal.map inferInstance pi hpi
  let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  have he : (normalChainQuotient pi.ker M).map e.toMonoidHom=I := by
    change (M.map (QuotientGroup.mk' pi.ker)).map e.toMonoidHom=M.map pi
    rw [Subgroup.map_map]
    rfl
  have hi : Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 (normalChainQuotient pi.ker M))≤1 :=
    (relativeCharacterAmbientCongr 2 e (normalChainQuotient pi.ker M) I he).finrank_eq.symm.le.trans
      (OddKernelCyclicUpperRelativeHead.relative_head_le_one beta hbeta hodd I)
  have hc := primeRelativeHead_chain_le (M ⊓ pi.ker) M 2 inf_le_left
  rw [primeRelativeHead_second_isomorphism 2 M pi.ker] at hc
  have hk := hkernel (M ⊓ pi.ker) inf_le_right
  omega
end SymmetricSubgroupAsymptotics.BinaryKernelOddCyclicTopRelativeHeads
