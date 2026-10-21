import SymmetricSubgroupAsymptotics.External.CFSG.Index
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.TransferInstance

/-!
# The CFSG exhaustiveness hypothesis

This file defines a proposition, not an axiom or a proof of classification.
`IsSimpleGroup` includes `Nontrivial`, so the one-element group is excluded;
abelian simple groups are included. All models and parameters live in Type 0.
The universe transfer theorem shows that the one proposition also classifies
finite groups in every higher universe, without a universe-polymorphic axiom.
-/

namespace CFSG

/-- Every nontrivial finite simple group is isomorphic to an explicit indexed model.
No order, simplicity, or two-generation property of the models is asserted here. -/
def CFSGClassification : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : Index, Nonempty (G ≃* i.Model)

/-- The same single hypothesis applies in every universe. -/
theorem CFSGClassification.classify.{u} (hCFSG : CFSGClassification)
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] :
    ∃ i : Index, Nonempty (G ≃* i.Model) := by
  obtain ⟨G₀, groupG₀, finiteG₀, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  letI : Group G₀ := groupG₀
  letI : Fintype G₀ := finiteG₀
  letI : IsSimpleGroup G₀ := e.symm.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := hCFSG G₀
  exact ⟨i, ⟨e.trans f⟩⟩

/-- Explicitly records the nontriviality convention used by the hypothesis. -/
theorem simple_group_nontrivial (G : Type*) [Group G] [IsSimpleGroup G] :
    Nontrivial G := inferInstance

end CFSG
