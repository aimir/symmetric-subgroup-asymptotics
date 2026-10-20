import SymmetricSubgroupAsymptotics.DegreeFiveDihedralModel

/-! # The degree-five affine classification from literal action coordinates -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace DegreeFiveAffineClassification

/-- The order-ten branch is the unique dihedral subgroup of the natural
affine group, after transport through the actual translation chart. -/
def dihedralModel
    (U : PreE7NonPairActionClass 5)
    (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
    (hcard : Nat.card (preE7NonPairAction 5 U) = 10) :
    PublishedDegreeFiveAffineModel U := by
  let f := DegreeFiveAffineCoordinates.embedding P 0
  have hf : Function.Injective f := DegreeFiveAffineCoordinates.embedding_injective P 0
  have hrange : Nat.card f.range = 10 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard
  have hhalf : f.range = DegreeFiveDihedralModel.half :=
    DegreeFiveDihedralModel.subgroup_card_ten_eq_half f.range hrange
  exact .dihedral ((MonoidHom.ofInjective hf).trans
    ((MulEquiv.subgroupCongr hhalf).trans DegreeFiveDihedralModel.halfEquiv))

/-- At order twenty the faithful affine embedding fills the whole natural
group. Its point chart retains exactly the literal relabelling required by
the marked `C4` consumer. -/
def frobeniusModel
    (U : PreE7NonPairActionClass 5)
    (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
    (hcard : Nat.card (preE7NonPairAction 5 U) = 20) :
    PublishedDegreeFiveAffineModel U := by
  let e := DegreeFiveAffineCoordinates.pointEquiv P 0
  let f := DegreeFiveAffineCoordinates.embedding P 0
  have hle : preE7NonPairAction 5 U ≤
      relabelSubgroup e (AffineModel.action F20.R).range := by
    intro g hg
    rw [mem_relabelSubgroup]
    refine ⟨f ⟨g, hg⟩, ?_⟩
    apply Equiv.ext
    intro v
    apply e.injective
    change e (AffineModel.action F20.R (f ⟨g, hg⟩) v) =
      e (e.symm (g (e v)))
    rw [e.apply_symm_apply]
    exact DegreeFiveAffineCoordinates.embedding_point P 0 ⟨g, hg⟩ v
  have hmodelcard : Nat.card
      (relabelSubgroup e (AffineModel.action F20.R).range) = 20 :=
    (Nat.card_congr
      (relabelModelEquiv (AffineModel.action F20.R)
        (AffineModel.action_injective F20.R) e rfl).toEquiv).trans F20.card_G
  refine .frobenius ⟨e, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [hmodelcard, hcard]

/-- The three degree-five models follow from the regular normal subgroup
and faithful action. Primitivity is part of the published interface, but
is stronger than this elementary classification needs. -/
theorem classification : PublishedDegreeFiveAffineClassification := by
  intro U P _hprimitive
  rcases card_cases U P with h | h | h
  · exact ⟨cyclicModel U h⟩
  · exact ⟨dihedralModel U P h⟩
  · exact ⟨frobeniusModel U P h⟩

end DegreeFiveAffineClassification
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
