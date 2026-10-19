import SymmetricSubgroupAsymptotics.PrimeCharacterOrderDivisibility
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralAbelianSupplement
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! An abelian odd kernel inside the actual derived subgroup cannot be
lost by an ambient-normal subgroup surjecting onto the upper quotient.
Binary relative heads therefore pass to proper upper normal images. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddDerivedKernelProperRelativeHead
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem proper_image {B R : Type} [Group B] [Finite B] [Group R]
    (beta : B →* R) (hbeta : Function.Surjective beta)
    (habel : IsMulCommutative beta.ker) (hderived : beta.ker≤commutator B)
    (M : Subgroup B) [M.Normal] (hne : M≠⊤) : M.map beta≠⊤ := by
  intro hfull
  have hsup : beta.ker ⊔ M=⊤ := by
    have h := congrArg (Subgroup.comap beta) hfull
    simpa only [Subgroup.comap_map_eq,Subgroup.comap_top,sup_comm] using h
  have hc := TwelvePointRemainingStructural.relativeRadicalQuotient_commutative
    2 beta.ker M hsup habel
  have hd : commutator B≤primeRelativeRadical 2 M :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hc
  have hk : beta.ker≤M := hderived.trans (hd.trans (primeRelativeRadical_le 2 M))
  exact hne (by simpa only [sup_eq_right.mpr hk] using hsup)

theorem relative_head_le_one {B R : Type} [Group B] [Finite B] [Group R] [Finite R]
    (beta : B →* R) (hbeta : Function.Surjective beta)
    (habel : IsMulCommutative beta.ker) (hderived : beta.ker≤commutator B)
    (hodd : IsPGroup 3 beta.ker)
    (hupper : ∀ (L : Subgroup R) [L.Normal], L≠⊤ →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤1)
    (M : Subgroup B) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  let I := M.map beta
  letI : I.Normal := Subgroup.Normal.map inferInstance beta hbeta
  have hi : I≠⊤ := proper_image beta hbeta habel hderived M hne
  let e := QuotientGroup.quotientKerEquivOfSurjective beta hbeta
  have he : (normalChainQuotient beta.ker M).map e.toMonoidHom=I := by
    change (M.map (QuotientGroup.mk' beta.ker)).map e.toMonoidHom=M.map beta
    rw [Subgroup.map_map]
    rfl
  have hI : Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 (normalChainQuotient beta.ker M))≤1 :=
    (relativeCharacterAmbientCongr 2 e (normalChainQuotient beta.ker M) I he).finrank_eq.symm.le.trans
      (hupper I hi)
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
end SymmetricSubgroupAsymptotics.OddDerivedKernelProperRelativeHead
