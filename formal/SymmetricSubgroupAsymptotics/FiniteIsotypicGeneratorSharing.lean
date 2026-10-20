import SymmetricSubgroupAsymptotics.FiniteSemisimpleSelectedGeneratorSharing
import SymmetricSubgroupAsymptotics.FiniteIsotypicCoordinates

/-! Canonical isotypic components have fully invariant complements, and
every finite selected collection shares the same generator slots. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

def isotypicComplement
    {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (c : isotypicComponents R M) : Submodule R M :=
  sSup (isotypicComponents R M \ {c.val})

theorem isotypicComplement_isCompl
    {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] (c : isotypicComponents R M) :
    IsCompl c.val (isotypicComplement c) := by
  have hdis : Disjoint c.val (isotypicComplement c) :=
    sSupIndep_isotypicComponents R M c.property
  have hsup : c.val⊔isotypicComplement c=⊤ := by
    apply top_unique
    rw [←sSup_isotypicComponents R M]
    apply sSup_le
    intro P hP
    by_cases he : P=c.val
    · rw [he]
      exact le_sup_left
    · have hmem : P ∈ isotypicComponents R M \ {c.val} := ⟨hP,he⟩
      have hle : P ≤ isotypicComplement c := le_sSup hmem
      exact hle.trans le_sup_right
  exact ⟨hdis,codisjoint_iff.mpr hsup⟩

theorem isotypicComplement_fullyInvariant
    {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (c : isotypicComponents R M) : (isotypicComplement c).IsFullyInvariant := by
  exact (fullyInvariantSubmodule R M).sSupClosed
    (fun P hP => Submodule.IsFullyInvariant.of_mem_isotypicComponents hP.1)

theorem moduleGeneratedBy_isotypic_selection
    {R M I : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] [Fintype I]
    (c : I → isotypicComponents R M) (hc : Function.Injective c)
    (t : ℕ) (hgen : ∀ i, ModuleGeneratedBy R (c i).val t) :
    ModuleGeneratedBy R (↥(⨆ i, (c i).val : Submodule R M)) t := by
  apply moduleGeneratedBy_selected_fullyInvariant_sum
    (fun i => (c i).val) (fun i => isotypicComplement (c i))
    (fun i => isotypicComplement_isCompl (c i))
    (fun i => Submodule.IsFullyInvariant.of_mem_isotypicComponents (c i).property)
    (fun i => isotypicComplement_fullyInvariant (c i)) ?_ t hgen
  intro i j hji
  apply le_sSup
  refine ⟨(c j).property,?_⟩
  intro he
  exact hji (hc (Subtype.ext he))

end SymmetricSubgroupAsymptotics
