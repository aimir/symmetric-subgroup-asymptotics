import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A proper-index bound for the SAME literal model transfers to the
least index of the actual simple factor and hence its primitive degree.
No classification or ordinary-generation hypothesis is added. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem least_index_ge {M : Type} [Group M] (e : D.Simple ≃* M) (m ell : ℕ)
    (hell : LeastProperIndex D.Simple ell)
    (hindex : ∀ H : Subgroup M, H ≠ ⊤ → m ≤ H.index) : m ≤ ell := by
  obtain ⟨H,hH,he⟩ := (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell).1
  exact (hindex H hH).trans_eq he

theorem degree_ge {M : Type} [Group M] (e : D.Simple ≃* M) (m : ℕ)
    (hindex : ∀ H : Subgroup M, H ≠ ⊤ → m ≤ H.index) : m ≤ Nat.card X := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  exact (least_index_ge D e m ell hell hindex).trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)

end SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport
