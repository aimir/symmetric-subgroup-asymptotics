import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCommonCentralizer
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowNormalizerSolvable

/-! The literal derived-positive group has centre of order two. Only the
three proved positive/derived probes are used, with no claim that they
generate the group. The original Tits Sylow result transports through the
already checked injective full-centre quotient map on this SAME subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentre
open CFSGReeFFourBinaryPositiveCommonCentralizer CFSGReeFFourDerivedPositiveFourProbes
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourAllParameterDerivedPositive
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourBinarySylowNormalizerSolvable
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedAmbientHom CFSGReeFFourOriginalPositiveSylow
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private def positiveProbe (i : Fin 4) : derivedPositive 0 :=
  ⟨derivedProbe 0 i,derivedProbe_mem_positive 0 i⟩

private theorem center_commute_probe (z : Subgroup.center (derivedPositive 0)) (i : Fin 4) :
    Commute z.val.val.val (probes 0 i) := by
  have hh := congrArg (fun a : derivedPositive 0 => a.val.val)
    (Subgroup.mem_center_iff.mp z.property (positiveProbe i))
  change z.val.val.val*(probes 0 i)=(probes 0 i)*z.val.val.val
  exact hh.symm

def centerToCommon (z : Subgroup.center (derivedPositive 0)) : CommonCentralizer :=
  ⟨z.val.val.val,z.val.property,center_commute_probe z 0,
    center_commute_probe z 2,center_commute_probe z 1⟩

theorem centerToCommon_injective : Function.Injective centerToCommon := by
  intro a b he
  have hh := congrArg (fun z : CommonCentralizer => z.val) he
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hh

theorem derivedPositive_center_card_le_two :
    Nat.card (Subgroup.center (derivedPositive 0)) ≤ 2 := by
  letI : Finite CommonCentralizer := Finite.of_injective parameterCode parameterCode_injective
  exact (Nat.card_le_card_of_injective centerToCommon centerToCommon_injective).trans
    card_commonCentralizer_le_two

theorem derivedPositive_center_card_eq_two :
    Nat.card (Subgroup.center (derivedPositive 0))=2 := by
  have hp : IsPGroup 2 (derivedPositive 0) :=
    (positiveSylow 0).isPGroup'.of_equiv (MulEquiv.subgroupCongr (positiveSylow_coe 0))
  letI : Nontrivial (derivedPositive 0) := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1<2048) derivedPositive_card_ge_2048)
  letI : Nontrivial (Subgroup.center (derivedPositive 0)) := hp.center_nontrivial
  have hl : 1<Nat.card (Subgroup.center (derivedPositive 0)) := Finite.one_lt_card
  exact Nat.le_antisymm derivedPositive_center_card_le_two (Nat.succ_le_of_lt hl)

theorem tits_positive_range_center_card_eq_two :
    Nat.card (Subgroup.center titsPositiveHom.range)=2 := by
  let e : derivedPositive 0 ≃* titsPositiveHom.range :=
    MonoidHom.ofInjective titsPositiveHom_injective
  have hc := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  exact hc.symm.trans derivedPositive_center_card_eq_two

private theorem positive_range_eq_map :
    titsPositiveHom.range=(derivedPositive 0).map (derivedReeHom 0) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.val,y.property,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩

theorem tits_positive_sylow_center_card_eq_two :
    Nat.card (Subgroup.center titsPositiveSylow)=2 := by
  have hs : (titsPositiveSylow : Subgroup CFSG.Models.Tits)=titsPositiveHom.range :=
    titsPositiveSylow_coe.trans positive_range_eq_map.symm
  let e : titsPositiveSylow ≃* titsPositiveHom.range := MulEquiv.subgroupCongr hs
  have hc := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  exact hc.trans tits_positive_range_center_card_eq_two

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentre
