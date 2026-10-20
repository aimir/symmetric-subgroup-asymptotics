import SymmetricSubgroupAsymptotics.Selected1542FirstMonolith
import SymmetricSubgroupAsymptotics.OriginalSixteenPreE7Representative

/-! The literal original generators determine an actual transitive nonbinary
sixteen-point action class. No finite527 index is asserted by this binding. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
open Non2UnipotentPrefixFiniteMenu

theorem original_transitive : MulAction.IsPretransitive Original (Fin 16) := by
  apply (MulAction.isPretransitive_iff_base (G := Original) (0 : Fin 16)).mpr
  intro x
  let g : Original := ((firstCenterOrbitWord x).map firstCenterOriginalGenerator).prod
  refine ⟨g,?_⟩
  change g.val 0=x
  have hg : g.val=((firstCenterOrbitWord x).map firstCenterGenerator).prod := by
    change Original.subtype (((firstCenterOrbitWord x).map firstCenterOriginalGenerator).prod)=_
    rw [map_list_prod,List.map_map]
    change ((firstCenterOrbitWord x).map (fun j => (firstCenterOriginalGenerator j).val)).prod=_
    simp only [firstCenterOriginalGenerator_val]
  rw [hg]
  exact firstCenter_orbit x

theorem original_nonbinary : ¬IsPGroup 2 Original := by
  intro h
  have hc := h.of_surjective originalCubic originalCubic_surjective
  have hcard : Nat.card CyclicThree=3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : CyclicThree ≃ ZMod 3),Nat.card_zmod]
  rcases hc.card_eq_or_dvd with he | he <;> norm_num [hcard] at he

def literalChart : OriginalSixteenPreE7Representative.Chart Original :=
  OriginalSixteenPreE7Representative.choose Original original_nonbinary original_transitive

def literalRepresentative : PreE7NonPairActionClass 16 := literalChart.index

def literalRepresentativeEquiv : preE7NonPairAction 16 literalRepresentative ≃* Original :=
  literalChart.groupEquiv.symm

theorem literal_point_conjugacy :
    MulAut.conj literalChart.conjugator • Original=
      preE7NonPairAction 16 literalRepresentative := literalChart.point_conjugacy

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
