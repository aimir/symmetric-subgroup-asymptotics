import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! Transport of the ordinary physical dependent-normal budget to the
actual marked source. Every relevant marked normal subgroup has mark zero,
maps into the SAME physical derived/tail-kernel intersection, and retains
its actual ambient normal-generator number. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedNormalBudgetTransport
open ActualMarkZeroNormalRank

variable {B M P : Type} [Group B] [Finite B] [CommGroup M] [Finite M] [Group P]
  (A : Subgroup (B × M)) (tail : PhysicalImage A →* P)

theorem physical_derived_eq : (commutator A).map (projection A)=commutator (PhysicalImage A) := by
  rw [map_commutator_eq,(projection A).range_eq_top_of_surjective (physical A).rangeRestrict_surjective]
  rfl

/-- The actual marked relevant normal subgroup maps to the ordinary
physical relevant subgroup, retaining the tail projection exactly. -/
theorem image_le_derived_tail (U : Subgroup A)
    (hU : U≤commutator A ⊓ (tail.comp (projection A)).ker) :
    U.map (projection A)≤commutator (PhysicalImage A) ⊓ tail.ker := by
  rintro x ⟨u,hu,rfl⟩
  constructor
  · rw [← physical_derived_eq A]
    exact ⟨u,(hU hu).1,rfl⟩
  · exact (hU hu).2

/-- Only the ordinary physical normal budget is a premise. The marked
budget required by arbitrary-normal-F RDT4.6 is DERIVED unchanged. -/
theorem marked_normal_budget (dN : ℕ)
    (hphysical : ∀ V : Subgroup (PhysicalImage A),V.Normal →
      V≤commutator (PhysicalImage A) ⊓ tail.ker →normalGen V≤dN) :
    ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ (tail.comp (projection A)).ker →normalGen U≤dN := by
  intro U hUn hU
  letI : U.Normal := hUn
  letI : (U.map (projection A)).Normal :=
    Subgroup.Normal.map inferInstance (projection A) (physical A).rangeRestrict_surjective
  rw [← derived_normal_rank_eq A U (hU.trans inf_le_left)]
  exact hphysical _ inferInstance (image_le_derived_tail A tail U hU)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedNormalBudgetTransport
