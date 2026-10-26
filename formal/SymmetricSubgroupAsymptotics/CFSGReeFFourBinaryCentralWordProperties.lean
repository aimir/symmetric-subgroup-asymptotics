import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCentralWord

/-! Realize the decoded original word by the unique nonidentity element
of the proved two-element centre of the literal derived-positive group.
This establishes original membership and centrality without a norm-matrix
faithfulness assumption or a list of exceptional-fixed individual roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralWordProperties
open CFSGReeFFourBinaryPositiveCentralWord CFSGReeFFourBinaryPositiveCentre
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourDerivedAmbientHom
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedAmbientHom

private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private theorem exists_nonidentity :
    ∃z : Subgroup.center (derivedPositive 0),z≠1 := by
  letI : Nontrivial (Subgroup.center (derivedPositive 0)) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (derivedPositive_center_card_eq_two.symm ▸ (by decide : 1<(2 : ℕ)))
  exact exists_ne 1

def centralSource : Subgroup.center (derivedPositive 0) :=
  Classical.choose exists_nonidentity

theorem centralSource_ne_one : centralSource≠1 :=
  Classical.choose_spec exists_nonidentity

theorem centralSource_value : centralSource.val.val.val=centralWord := by
  apply center_nonidentity_eq
  intro h
  exact centralSource_ne_one (Subtype.ext (Subtype.ext (Subtype.ext h)))

theorem centralWord_mem_derived : centralWord∈commutator (originalModelFixed 0) :=
  centralSource_value ▸ centralSource.val.val.property

theorem centralWord_mem_positive : centralWord∈fixedPositive 0 :=
  centralSource_value ▸ centralSource.val.property

theorem centralWord_ne_one : centralWord≠1 := by
  intro h
  have he : centralSource.val.val.val=1 := centralSource_value.trans h
  exact centralSource_ne_one (Subtype.ext (Subtype.ext (Subtype.ext he)))

theorem centralWord_commutes_positive (u : derivedPositive 0) :
    Commute centralWord u.val.val := by
  have hh := congrArg (fun x : derivedPositive 0 => x.val.val)
    (Subgroup.mem_center_iff.mp centralSource.property u)
  have hc : Commute centralSource.val.val.val u.val.val := hh.symm
  rw [centralSource_value] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryCentralWordProperties
