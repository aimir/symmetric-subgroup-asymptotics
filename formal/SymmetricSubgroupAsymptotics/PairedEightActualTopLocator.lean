import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PermutationConjugateTopChart
import SymmetricSubgroupAsymptotics.PairedEightActualKernelModel
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! The sole published degree-eight classification is specialized to the
24 pinned canonical actions, then transferred through checked literal
conjugacies. The actual pair points and coordinate conjugator are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PairedEightActualTopLocator
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoPairedEightSharedTops

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

/-- No binary top branch exists for a nonbinary physical pair action. -/
theorem top_nonbinary (hU : ¬IsPGroup 2 U) : ¬IsPGroup 2 F.top.range :=
  F.top_not_isPGroup hU

/-- Every actual transitive nonbinary pair top has an action-coordinate
match to the literal catalogue, not merely an abstract group isomorphism. -/
theorem exists_actual_model
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    [MulAction.IsPretransitive U X] (hU : ¬IsPGroup 2 U) :
    ∃ (j : Fin 24) (e : F.top.range ≃* (interface j).top)
      (coords : Fin 8 ≃ Fin 8),
      ∀ (p : F.top.range) (i : Fin 8),
        coords ((p : Equiv.Perm (Fin 8)) i)=
          (e p : Equiv.Perm (Fin 8)) (coords i) := by
  have htrans : PermutationSubgroupTransitive F.top.range := by
    letI := F.top_pretransitive
    intro i k
    obtain ⟨p,hp⟩ := MulAction.exists_smul_eq F.top.range i k
    exact ⟨p.val,p.property,hp⟩
  obtain ⟨j,g,hg⟩ := DegreeEightCanonicalCatalogue.originalClassification published
    F.top.range htrans (F.top_not_isPGroup hU)
  refine ⟨j,PermutationConjugateTopChart.groupChart F.top.range (interface j).top g hg,
    g,?_⟩
  intro p i
  exact PermutationConjugateTopChart.equivariant F.top.range (interface j).top g hg p i

end SymmetricSubgroupAsymptotics.PairedEightActualTopLocator
