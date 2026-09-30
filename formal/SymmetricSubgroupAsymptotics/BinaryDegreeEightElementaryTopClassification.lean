import SymmetricSubgroupAsymptotics.BinaryActionCoverage8
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.GeneratedSplitTopNormals.ElementaryIndexTwoExclusions
import SymmetricSubgroupAsymptotics.GeneratedSplitTopNormals.SelectedElementaryAxes

/-!
# Degree-eight tops with an elementary index-two axis

The degree-sixteen split residual supplies a transitive binary top on eight
blocks together with a normal index-two subgroup of exponent two.  The
complete original-point action registry and the complete normal registries
show that only the literal actions `8T9`, `8T10`, and `8T18` can occur.

The finite exclusions retain a concrete non-involution in every rejected
index-two normal subgroup.  This file only transports those witnesses through
the original faithful actions and the one ambient conjugation supplied by the
action registry.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryTopClassification

open SymmetricSubgroupAsymptotics
open BinaryActionRegistry8

/-- The three literal degree-eight actions which possess a normal index-two
subgroup of exponent two. -/
def elementaryTops (i : Fin 3) : Subgroup (Equiv.Perm (Fin 8)) :=
  ![Subgroup.closure (Set.range BinaryMenuCayley8T9.generators),
    Subgroup.closure (Set.range BinaryMenuCayley8T10.generators),
    Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)] i

/-- The retained nontransitive elementary axis inside `8T9`. -/
def elementaryAxis8T9 : Subgroup (elementaryTops 0) :=
  BinarySelectedAxis8T9.selectedAxis

/-- The retained nontransitive elementary axis inside `8T10`. -/
def elementaryAxis8T10 : Subgroup (elementaryTops 1) :=
  BinarySelectedAxis8T10.selectedAxis

/-- The retained nontransitive elementary axis inside `8T18`. -/
def elementaryAxis8T18 : Subgroup (elementaryTops 2) :=
  BinarySelectedAxis8T18.selectedAxis

private theorem transitive_conjugate_iff {Ω : Type*}
    (g : Equiv.Perm Ω) (A : Subgroup (Equiv.Perm Ω)) :
    PermutationSubgroupTransitive (MulAut.conj g • A) ↔
      PermutationSubgroupTransitive A := by
  constructor
  · intro h
    have h' := permutationSubgroupTransitive_conjugate g⁻¹
      (MulAut.conj g • A) h
    simpa [← mul_smul] using h'
  · exact permutationSubgroupTransitive_conjugate g A

/-- An exact literal-axis classifier transports through the same ambient
conjugation used to classify the top action. -/
private theorem selected_axis_after_conjugacy
    {T U : Subgroup (Equiv.Perm (Fin 8))}
    (g : Equiv.Perm (Fin 8)) (hg : MulAut.conj g • T=U)
    (H : Subgroup T) [H.Normal]
    (hindex : H.index=2) (hexponent : ∀ x : H,x^2=1)
    (hnottrans : ¬PermutationSubgroupTransitive (H.map T.subtype))
    (selected : Subgroup U)
    (hcomplete : ∀ (N : Subgroup U) [N.Normal], N.index=2 →
      (∀ x : N,x^2=1) →
      ¬PermutationSubgroupTransitive (N.map U.subtype) → N=selected) :
    actionConjugacyNormal g hg H=selected := by
  let e : T ≃* U := actionConjugacyEquiv g hg
  let N : Subgroup U := actionConjugacyNormal g hg H
  have hindexN : N.index=2 :=
    (Subgroup.index_map_equiv H e).trans hindex
  let eH : H ≃* N :=
    (H.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr rfl)
  have hexponentN : ∀ x : N,x^2=1 := by
    intro x
    have hp := congrArg eH (hexponent (eH.symm x))
    simpa only [map_pow,map_one,MulEquiv.apply_symm_apply] using hp
  apply hcomplete N hindexN hexponentN
  rw [actionConjugacyNormal_ambient]
  intro h
  apply hnottrans
  exact (transitive_conjugate_iff g _).mp h

private def actionOrder (i : Fin 26) : ℕ :=
  ![8,8,8,8,8,16,16,16,16,16,16,32,32,32,32,32,32,32,32,
    64,64,64,64,64,64,128] i

private theorem action_card (i : Fin 26) :
    Nat.card (actions i)=actionOrder i := by
  fin_cases i
  · exact BinaryMenuCayley8T1.exact_card
  · exact BinaryMenuCayley8T2.exact_card
  · exact BinaryMenuCayley8T3.exact_card
  · exact BinaryMenuCayley8T4.exact_card
  · exact BinaryMenuCayley8T5.exact_card
  · exact BinaryMenuCayley8T6.exact_card
  · exact BinaryMenuCayley8T7.exact_card
  · exact BinaryMenuCayley8T8.exact_card
  · exact BinaryMenuCayley8T9.exact_card
  · exact BinaryMenuCayley8T10.exact_card
  · exact BinaryMenuCayley8T11.exact_card
  · exact BinaryMenuCayley8T15.exact_card
  · exact BinaryMenuCayley8T16.exact_card
  · exact BinaryMenuCayley8T17.exact_card
  · exact BinaryMenuCayley8T18.exact_card
  · exact BinaryMenuCayley8T19.exact_card
  · exact BinaryMenuCayley8T20.exact_card
  · exact BinaryMenuCayley8T21.exact_card
  · exact BinaryMenuCayley8T22.exact_card
  · exact BinaryMenuCayley8T26.exact_card
  · exact BinaryMenuCayley8T27.exact_card
  · exact BinaryMenuCayley8T28.exact_card
  · exact BinaryMenuCayley8T29.exact_card
  · exact BinaryMenuCayley8T30.exact_card
  · exact BinaryMenuCayley8T31.exact_card
  · exact BinaryMenuCayley8T35.exact_card

/-- A complete normal registry whose index-two rows all retain a
non-involution rules out an exponent-two index-two normal after any faithful
group equivalence. -/
private theorem impossible_of_registry
    {G H ι I : Type*} [Group G] [Finite G] [Group H]
    {generators : ι → G}
    {hgen : Subgroup.closure (Set.range generators)=⊤}
    {states : I → BinaryNormalState generators}
    (registry : BinaryNormalRegistry generators hgen states)
    (hG : IsPGroup 2 G) (e : G ≃* H)
    (N : Subgroup H) (hN : N.Normal)
    (hindex : N.index=2) (hexponent : ∀ x : N, x^2=1)
    (hexclude : ∀ i, (states i).quotientCount≠2 ∨
      ∃ x : (states i).kernel, x^2≠1) : False := by
  letI : N.Normal := hN
  obtain ⟨i,hi⟩ := registry.complete_map_of_equiv hG e N
  rcases hexclude i with hquotient | ⟨x,hx⟩
  · apply hquotient
    rw [← (states i).index_eq_quotientCount]
    calc
      (states i).kernel.index =
          ((states i).kernel.map e.toMonoidHom).index :=
        (Subgroup.index_map_equiv (states i).kernel e).symm
      _ = N.index := congrArg Subgroup.index hi
      _ = 2 := hindex
  · let en : (states i).kernel ≃* N :=
      ((states i).kernel.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hi)
    have hpull := congrArg en.symm (hexponent (en x))
    apply hx
    simpa only [map_pow,map_one,MulEquiv.symm_apply_apply] using hpull

/-- A transitive degree-eight 2-group of order 16 or 32 with a normal
index-two exponent-two subgroup is ambient-conjugate to exactly one of the
three retained literal actions (existence is all that is needed here). -/
theorem complete
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (hT : IsPGroup 2 T) (htrans : PermutationSubgroupTransitive T)
    (H : Subgroup T) [H.Normal]
    (horder : Nat.card T=16 ∨ Nat.card T=32)
    (hindex : H.index=2) (hexponent : ∀ x : H, x^2=1) :
    ActionRegistryCovered elementaryTops T := by
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete T hT htrans
  let e : T ≃* actions i := actionConjugacyEquiv g hg
  let N : Subgroup (actions i) := actionConjugacyNormal g hg H
  have hnormalN : N.Normal := by
    dsimp [N]
    infer_instance
  let eH : H ≃* N :=
    (H.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr rfl)
  have hindexN : N.index=2 :=
    (Subgroup.index_map_equiv H e).trans hindex
  have hexponentN : ∀ x : N, x^2=1 := by
    intro x
    have hp := congrArg eH (hexponent (eH.symm x))
    simpa only [map_pow,map_one,MulEquiv.apply_symm_apply] using hp
  have hcard : Nat.card T=actionOrder i :=
    (Nat.card_congr e.toEquiv).trans (action_card i)
  have hallowed : actionOrder i=16 ∨ actionOrder i=32 := by
    rcases horder with horder | horder
    · exact Or.inl (hcard.symm.trans horder)
    · exact Or.inr (hcard.symm.trans horder)
  fin_cases i
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · letI : Group BinaryNormal8T6.Source := BinaryMenuCayley8T6.group
    exact (impossible_of_registry BinaryNormal8T6.registry
      BinaryNormal8T6.source_isPGroup BinaryMenuCayley8T6.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T6.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T7.Source := BinaryMenuCayley8T7.group
    exact (impossible_of_registry BinaryNormal8T7.registry
      BinaryNormal8T7.source_isPGroup BinaryMenuCayley8T7.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T7.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T8.Source := BinaryMenuCayley8T8.group
    exact (impossible_of_registry BinaryNormal8T8.registry
      BinaryNormal8T8.source_isPGroup BinaryMenuCayley8T8.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T8.no_elementary_index_two).elim
  · exact ⟨0,g,by simpa [elementaryTops,actions] using hg⟩
  · exact ⟨1,g,by simpa [elementaryTops,actions] using hg⟩
  · letI : Group BinaryNormal8T11.Source := BinaryMenuCayley8T11.group
    exact (impossible_of_registry BinaryNormal8T11.registry
      BinaryNormal8T11.source_isPGroup BinaryMenuCayley8T11.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T11.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T15.Source := BinaryMenuCayley8T15.group
    exact (impossible_of_registry BinaryNormal8T15.registry
      BinaryNormal8T15.source_isPGroup BinaryMenuCayley8T15.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T15.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T16.Source := BinaryMenuCayley8T16.group
    exact (impossible_of_registry BinaryNormal8T16.registry
      BinaryNormal8T16.source_isPGroup BinaryMenuCayley8T16.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T16.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T17.Source := BinaryMenuCayley8T17.group
    exact (impossible_of_registry BinaryNormal8T17.registry
      BinaryNormal8T17.source_isPGroup BinaryMenuCayley8T17.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T17.no_elementary_index_two).elim
  · exact ⟨2,g,by simpa [elementaryTops,actions] using hg⟩
  · letI : Group BinaryNormal8T19.Source := BinaryMenuCayley8T19.group
    exact (impossible_of_registry BinaryNormal8T19.registry
      BinaryNormal8T19.source_isPGroup BinaryMenuCayley8T19.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T19.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T20.Source := BinaryMenuCayley8T20.group
    exact (impossible_of_registry BinaryNormal8T20.registry
      BinaryNormal8T20.source_isPGroup BinaryMenuCayley8T20.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T20.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T21.Source := BinaryMenuCayley8T21.group
    exact (impossible_of_registry BinaryNormal8T21.registry
      BinaryNormal8T21.source_isPGroup BinaryMenuCayley8T21.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T21.no_elementary_index_two).elim
  · letI : Group BinaryNormal8T22.Source := BinaryMenuCayley8T22.group
    exact (impossible_of_registry BinaryNormal8T22.registry
      BinaryNormal8T22.source_isPGroup BinaryMenuCayley8T22.originalEquiv
      N hnormalN hindexN hexponentN BinaryNormal8T22.no_elementary_index_two).elim
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed
  · norm_num [actionOrder] at hallowed

/-- If the elementary index-two axis has two orbits, the classification
retains the exact literal axis as well as the top action. -/
theorem complete_axis
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (hT : IsPGroup 2 T) (htrans : PermutationSubgroupTransitive T)
    (H : Subgroup T) [H.Normal]
    (horder : Nat.card T=16 ∨ Nat.card T=32)
    (hindex : H.index=2) (hexponent : ∀ x : H,x^2=1)
    (hnottrans : ¬PermutationSubgroupTransitive (H.map T.subtype)) :
    (∃ (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • T=elementaryTops 0),
      actionConjugacyNormal g hg H=elementaryAxis8T9) ∨
    (∃ (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • T=elementaryTops 1),
      actionConjugacyNormal g hg H=elementaryAxis8T10) ∨
    (∃ (g : Equiv.Perm (Fin 8))
      (hg : MulAut.conj g • T=elementaryTops 2),
      actionConjugacyNormal g hg H=elementaryAxis8T18) := by
  obtain ⟨i,g,hg⟩ := complete T hT htrans H horder hindex hexponent
  fin_cases i
  · left
    refine ⟨g,hg,selected_axis_after_conjugacy g hg H hindex hexponent
      hnottrans elementaryAxis8T9 ?_⟩
    intro N hnormal hindexN hexponentN hnottransN
    letI : N.Normal := hnormal
    exact @BinarySelectedAxis8T9.complete N hnormal hindexN hexponentN hnottransN
  · right; left
    refine ⟨g,hg,selected_axis_after_conjugacy g hg H hindex hexponent
      hnottrans elementaryAxis8T10 ?_⟩
    intro N hnormal hindexN hexponentN hnottransN
    letI : N.Normal := hnormal
    exact @BinarySelectedAxis8T10.complete N hnormal hindexN hexponentN hnottransN
  · right; right
    refine ⟨g,hg,selected_axis_after_conjugacy g hg H hindex hexponent
      hnottrans elementaryAxis8T18 ?_⟩
    intro N hnormal hindexN hexponentN hnottransN
    letI : N.Normal := hnormal
    exact @BinarySelectedAxis8T18.complete N hnormal hindexN hexponentN hnottransN

/-- A compact interface for the exact top-and-axis result. -/
def ExactAxisCovered (T : Subgroup (Equiv.Perm (Fin 8)))
    (H : Subgroup T) : Prop :=
  (∃ (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • T=elementaryTops 0),
    actionConjugacyNormal g hg H=elementaryAxis8T9) ∨
  (∃ (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • T=elementaryTops 1),
    actionConjugacyNormal g hg H=elementaryAxis8T10) ∨
  (∃ (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • T=elementaryTops 2),
    actionConjugacyNormal g hg H=elementaryAxis8T18)

/-- Compact form of `complete_axis`, used by the degree-sixteen split
closure. -/
theorem complete_exact_axis
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (hT : IsPGroup 2 T) (htrans : PermutationSubgroupTransitive T)
    (H : Subgroup T) [H.Normal]
    (horder : Nat.card T=16 ∨ Nat.card T=32)
    (hindex : H.index=2) (hexponent : ∀ x : H,x^2=1)
    (hnottrans : ¬PermutationSubgroupTransitive (H.map T.subtype)) :
    ExactAxisCovered T H :=
  complete_axis T hT htrans H horder hindex hexponent hnottrans

end SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryTopClassification
