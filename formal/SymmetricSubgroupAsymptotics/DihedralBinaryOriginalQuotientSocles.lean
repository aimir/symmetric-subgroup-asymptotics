import SymmetricSubgroupAsymptotics.DihedralTwelveProperNormalHead
import SymmetricSubgroupAsymptotics.RelativeHeadAbelianSupplementCyclicCoverCompatible
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralOriginalQuotientSocles

/-! Proper top images share the exact cyclic pair-kernel position with
one top position. Full top images use the actual two-cyclic abelianization
cover. Both feed the existing original faithful twelve-point socle theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralBinaryOriginalQuotientSocles
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G B C D : Type} [Group G] [Finite G] [Group B] [Finite B]
    [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (beta : B →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hB : Nat.card B=12) (hker : Nat.card beta.ker=2)
    (pi : G →* B) (hpi : Function.Surjective pi)
    (hK : IsMulCommutative pi.ker)
    (hkernel : ∀ (L : Subgroup G) [L.Normal], L≤pi.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤1)
    (cover : C × D →* G ⧸ commutator G) (hcover : Function.Surjective cover)

include hbeta hB hker hpi hK hkernel hcover in
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
        (primeRelativeCharacters 2 (normalChainQuotient pi.ker M))≤1 :=
      (relativeCharacterAmbientCongr 2 e (normalChainQuotient pi.ker M) I he).finrank_eq.symm.le.trans
        (DihedralTwelveProperNormalHead.relative_head_le_one beta hbeta hB hker I hfull)
    have hc := primeRelativeHead_chain_le (M ⊓ pi.ker) M 2 inf_le_left
    rw [primeRelativeHead_second_isomorphism 2 M pi.ker] at hc
    exact hc.trans (by have hk := hkernel (M ⊓ pi.ker) inf_le_right; omega)

include hbeta hB hker hpi hK hkernel hcover in
theorem quotientSocle {X : Type} [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hX : Nat.card X=12)
    (hKtwo : IsPGroup 2 pi.ker) (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) 2 := by
  have hb : Function.Surjective (beta.comp pi) := hbeta.comp hpi
  have ht : IsPGroup 2 beta.ker := IsPGroup.of_card (n := 1) (by simpa using hker)
  have hk : IsPGroup 2 (beta.comp pi).ker := ht.comap_of_ker_isPGroup pi hKtwo
  exact TwelvePointRemainingStructural.quotientSocle_two_of_original_symmetricThree hX
    (beta.comp pi) hb hk
    (relative_head_le_two beta hbeta hB hker pi hpi hK hkernel cover hcover) N

end SymmetricSubgroupAsymptotics.DihedralBinaryOriginalQuotientSocles
