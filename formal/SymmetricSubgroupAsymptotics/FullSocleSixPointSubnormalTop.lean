import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses

/-! A literal six-point permutation group with one original full socle
factor of order360 contains the actual alternating subgroup. Its socle
image has index2 inside the SAME symmetric group; no exceptional model
identification or primitive-action catalogue is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FullSocleSixPointSubnormalTop
open PrimitiveSocleRawStructure

theorem subnormal_of_order_threeSixty {X : Type} [Finite X]
    (P : Subgroup (Equiv.Perm X)) (E : NonaffineData P X)
    (hk : E.factorCount=1) (hcardS : Nat.card E.Simple=360)
    (hn : Nat.card X=6) : P.IsSubnormal := by
  letI : Fintype X := Fintype.ofFinite X
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hn];decide)
  let N : Subgroup (Equiv.Perm X) := (finiteGroupSocle P).map P.subtype
  have hsocle : Nat.card (finiteGroupSocle P)=360 :=
    (Nat.card_congr (E.oneFactorEquiv hk).toEquiv).trans hcardS
  have hNcard : Nat.card N=360 :=
    (Nat.card_congr ((finiteGroupSocle P).equivMapOfInjective P.subtype
      Subtype.val_injective).toEquiv).symm.trans hsocle
  have hperm : Nat.card (Equiv.Perm X)=720 := by rw [Nat.card_perm,hn];decide
  have hidx : N.index=2 := by
    have hh := N.card_mul_index
    rw [hNcard,hperm] at hh
    omega
  have hN : N=alternatingGroup X :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have hle : alternatingGroup X≤P := by
    rw [←hN]
    rintro _ ⟨g,hg,rfl⟩
    exact g.property
  rcases AlmostSimpleIndexTwoSubnormalClasses.containing_simple_index_two
      (alternatingGroup X) P alternatingGroup.index_eq_two hle with hAlt|hTop
  · rw [hAlt]
    exact Subgroup.Normal.isSubnormal inferInstance
  · rw [hTop]
    exact Subgroup.IsSubnormal.top

end SymmetricSubgroupAsymptotics.FullSocleSixPointSubnormalTop
