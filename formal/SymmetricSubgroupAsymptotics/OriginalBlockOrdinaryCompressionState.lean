import SymmetricSubgroupAsymptotics.ActualWreathChiefHalfOrderBudget
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-! An independent initial ordinary-compression state on the ORIGINAL
permutation subgroup and its actual minimal block. The state carries an
unconditionally full tuple enumerating the finite source, not a tuple
chosen from a Tracey/McIver-Neumann bound. Its quantitative tuple length
is never used in the ordinary recurrence. Original degree, local component,
top range, and correlated faithful wreath embedding are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

def initialState : ActualWreathCompressionState block.Top block.Points := by
  classical
  exact {
    A := J
    D := block.Component
    groupA := inferInstance
    finiteA := inferInstance
    groupD := inferInstance
    finiteD := inferInstance
    rho := ActualBlockWreathEmbedding.embedding block.map block.map_equivariant block.base
    rho_injective := ActualBlockWreathEmbedding.embedding_injective
      block.map block.map_equivariant block.base
    sourceDegree := n
    generatorCount := Nat.card J
    generators := (Finite.equivFin J).symm
    generators_full := by
      rw [Set.range_eq_univ.mpr (Finite.equivFin J).symm.surjective,
        Subgroup.closure_univ]
    sectionalRank := by
      intro p hp K
      exact primeRank_le_of_subgroup p J K
    top_surjective := by
      intro q
      obtain ⟨a, ha⟩ := q.property
      refine ⟨a, Subtype.ext ?_⟩
      simpa only [ActualBlockWreathEmbedding.embedding] using ha
    top_pretransitive := block.top_pretransitive
    fullComponent := ActualBlockWreathEmbedding.fullComponent
      block.map block.map_equivariant block.base }

/-- The genuine ordinary chief cost and strictly smaller top belong to
the same original action; neither numerical bound is assumed. -/
theorem exists_actual_cost (i : block.Points) :
    ∃ c : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i (initialState J block) c ∧
      MarkedC4.genRank J ≤ c + MarkedC4.genRank block.Top := by
  obtain ⟨c, hc⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost
    i (initialState J block)
  exact ⟨c, hc, ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hc⟩

theorem source_genRank_two_pow_le (i : block.Points) :
    2 ^ (2 * MarkedC4.genRank J) ≤
      Nat.card block.Component ^ Nat.card block.Points *
        2 ^ (2 * MarkedC4.genRank block.Top) := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have h := ActualWreathChiefHalfOrderBudget.source_genRank_two_pow_le
    (initialState J block) i hI
  simpa only [Fintype.card_eq_nat_card] using h

theorem exists_actual_generating_finset (i : block.Points) :
    ∃ c : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i (initialState J block) c ∧
      ∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
        F.card ≤ c + MarkedC4.genRank block.Top :=
  ActualWreathOrdinaryChiefRecurrence.exists_generating_finset i (initialState J block)

end SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
