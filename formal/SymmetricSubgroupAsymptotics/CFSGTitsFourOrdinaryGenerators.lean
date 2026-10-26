import SymmetricSubgroupAsymptotics.CFSGTitsFiveOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeOuterCommute

/-! Four literal generators determine homomorphisms from the actual
binary derived group and its full-centre Tits quotient. The remaining
Schreier conjugate is recovered from the whole negative-outer
commutation identity, rather than a searched matrix word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTitsFourOrdinaryGenerators
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourMiddleNegativeOuterCommute CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourOuterThreeWord
private abbrev D := commutator (originalModelFixed 0)
open CFSGReeFFourBinaryDerivedGeneration CFSGReeFFourBinaryOuterSaving
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourWholeOuterMiddleRelation

def derivedGenerators : Fin 4 → D := ![
  ⟨outerInvolution 0,outer_mem_derived 0⟩,
  ⟨outerFixedWeyl 0,outer_weyl_mem_derived 0 (outer_mem_derived 0)⟩,
  ⟨middleFixedWeyl 0,middle_weyl_mem_derived 0⟩,
  ⟨(fourCycle 0)^2,square_mem_derived 0⟩]

theorem derivedGenerators_closure :
    Subgroup.closure (Set.range derivedGenerators)=⊤ := by
  let H : Subgroup D := Subgroup.closure (Set.range derivedGenerators)
  let L : Subgroup (originalModelFixed 0) := H.map D.subtype
  have hmem (i : Fin 4) : (derivedGenerators i : originalModelFixed 0)∈L :=
    ⟨derivedGenerators i,Subgroup.subset_closure ⟨i,rfl⟩,rfl⟩
  have hx : outerInvolution 0∈L := hmem 0
  have hoW : outerFixedWeyl 0∈L := hmem 1
  have hm : middleFixedWeyl 0∈L := hmem 2
  have hs : (fourCycle 0)^2∈L := hmem 3
  have hr : fiveWord 0∈L := L.mul_mem hm hs
  have hq : fiveWord 0*outerInvolution 0*(fiveWord 0)⁻¹∈L :=
    L.mul_mem (L.mul_mem hr hx) (L.inv_mem hr)
  have hn : negativeOuter 0∈L := L.mul_mem (L.mul_mem hoW hx) (L.inv_mem hoW)
  have hyo : fourCycle 0*outerFixedWeyl 0*(fourCycle 0)⁻¹∈L := by
    rw [middle_conjugate_outerWeyl]
    exact L.mul_mem (L.mul_mem hq hn) hq
  have hyx : fourCycle 0*outerInvolution 0*(fourCycle 0)⁻¹∈L :=
    outer_middle_conjugate_mem 0 L hx hr
  have hym : fourCycle 0*middleFixedWeyl 0*(fourCycle 0)⁻¹∈L := by
    have he : fourCycle 0*middleFixedWeyl 0*(fourCycle 0)⁻¹=
        (fiveWord 0)^2*((fourCycle 0)^2)⁻¹ := by
      calc
        _=(fourCycle 0*fiveWord 0*(fourCycle 0)⁻¹)*((fourCycle 0)^2)⁻¹ := by
          dsimp only [fiveWord]
          group
        _=_ := by rw [fiveWord_conjugate]
    rw [he]
    exact L.mul_mem (L.pow_mem hr 2) (L.inv_mem hs)
  let S : Set (originalModelFixed 0) :=
    {outerInvolution 0,outerFixedWeyl 0,middleFixedWeyl 0}
  have hgen : Subgroup.closure (S∪{fourCycle 0})=⊤ := by
    apply subgroup_eq_top_of_four_generators
    · exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.subset_closure (Or.inl (Or.inr (Or.inl rfl)))
    · exact Subgroup.subset_closure (Or.inl (Or.inr (Or.inr rfl)))
  have hSchreier : DerivedTwoCosetGeneratorContainment.generatedSubgroup S (fourCycle 0)≤L := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases hz with (hz|⟨s,hz,rfl⟩)|hz
    · rcases hz with rfl|rfl|rfl
      · exact hx
      · exact hoW
      · exact hm
    · rcases hz with rfl|rfl|rfl
      · exact hyx
      · exact hyo
      · exact hym
    · have he : z=(fourCycle 0)^2 := hz
      exact he ▸ hs
  have hD : D≤L :=
    (DerivedTwoCosetGeneratorContainment.commutator_le_generatedSubgroup
      S (fourCycle 0) hgen).trans hSchreier
  apply top_unique
  intro z _
  obtain ⟨a,ha,he⟩ := hD z.property
  exact (Subtype.ext he : a=z) ▸ ha

def titsGenerators : Fin 4 → CFSG.Models.Tits :=
  fun i => derivedReeHom 0 (derivedGenerators i)

theorem titsGenerators_closure : Subgroup.closure (Set.range titsGenerators)=⊤ := by
  have he : Set.range titsGenerators=(derivedReeHom 0) '' Set.range derivedGenerators := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨derivedGenerators i,⟨i,rfl⟩,rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [he,←MonoidHom.map_closure,derivedGenerators_closure]
  exact Subgroup.map_top_of_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)

theorem hom_ext {G : Type*} [Group G] (f g : CFSG.Models.Tits →* G)
    (h : ∀ i : Fin 4,f (titsGenerators i)=g (titsGenerators i)) : f=g := by
  apply MonoidHom.eq_of_eqOn_dense titsGenerators_closure
  rintro _ ⟨i,rfl⟩
  exact h i

theorem tits_genRank_le_four : MarkedC4.genRank CFSG.Models.Tits≤4 := by
  let T : Finset CFSG.Models.Tits := Finset.univ.image titsGenerators
  have ht : (T : Set CFSG.Models.Tits)=Set.range titsGenerators := by
    simp only [T,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hc : Subgroup.closure (T : Set CFSG.Models.Tits)=⊤ := by
    rw [ht,titsGenerators_closure]
  exact (MarkedC4.genRank_le hc).trans
    (Finset.card_image_le.trans (by simp))

end SymmetricSubgroupAsymptotics.CFSGTitsFourOrdinaryGenerators
