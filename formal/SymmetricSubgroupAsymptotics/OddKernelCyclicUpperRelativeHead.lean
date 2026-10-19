import SymmetricSubgroupAsymptotics.OddDerivedKernelProperRelativeHead
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddKernelCyclicUpperRelativeHead
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
theorem relative_head_le_one {B R : Type} [Group B] [Finite B] [Group R] [Finite R]
    (beta : B →* R) (hbeta : Function.Surjective beta)
    (hodd : IsPGroup 3 beta.ker)
    [IsCyclic R]
    (M : Subgroup B) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  let I := M.map beta
  letI : I.Normal := Subgroup.Normal.map inferInstance beta hbeta
  let e := QuotientGroup.quotientKerEquivOfSurjective beta hbeta
  have he : (normalChainQuotient beta.ker M).map e.toMonoidHom=I := by
    change (M.map (QuotientGroup.mk' beta.ker)).map e.toMonoidHom=M.map beta
    rw [Subgroup.map_map]
    rfl
  have hI : Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 (normalChainQuotient beta.ker M))≤1 :=
    (relativeCharacterAmbientCongr 2 e (normalChainQuotient beta.ker M) I he).finrank_eq.symm.le.trans
      ((Submodule.finrank_le _).trans (primeSectionalRankBound_cyclic 2 R I))
  have hP : IsPGroup 3 (M ⊓ beta.ker : Subgroup B) :=
    hodd.of_injective (Subgroup.inclusion (inf_le_right : M ⊓ beta.ker≤beta.ker))
      (Subgroup.inclusion_injective (inf_le_right : M ⊓ beta.ker≤beta.ker))
  obtain ⟨a,ha⟩ := hP.exists_card_eq
  have hzero : Module.finrank (ZMod 2) (PrimeCharacters 2 (M ⊓ beta.ker : Subgroup B))=0 := by
    have hd := primeCharacters_pow_finrank_dvd_card 2 (M ⊓ beta.ker : Subgroup B)
    rw [ha] at hd
    by_contra hn
    have hp : 2∣2^Module.finrank (ZMod 2)
        (PrimeCharacters 2 (M ⊓ beta.ker : Subgroup B)) := by
      simpa using Nat.pow_dvd_pow 2 (show 1≤Module.finrank (ZMod 2)
        (PrimeCharacters 2 (M ⊓ beta.ker : Subgroup B)) from by omega)
    have ht : 2∣3^a := hp.trans hd
    have : 2∣3 := Nat.prime_two.dvd_of_dvd_pow ht
    norm_num at this
  have hrel : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (M ⊓ beta.ker))=0 := by
    have h := Submodule.finrank_le (primeRelativeCharacters 2 (M ⊓ beta.ker))
    rw [hzero] at h
    omega
  have hc := primeRelativeHead_chain_le (M ⊓ beta.ker) M 2 inf_le_left
  rw [hrel,zero_add,primeRelativeHead_second_isomorphism 2 M beta.ker] at hc
  exact hc.trans hI

end SymmetricSubgroupAsymptotics.OddKernelCyclicUpperRelativeHead
