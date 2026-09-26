import SymmetricSubgroupAsymptotics.PrimeFrattiniSurjection
import Mathlib.GroupTheory.Commutator.Basic

/-! Equality of the actual prime-evaluation kernel and derived subgroup
passes to actual epimorphic images and literal quotients. The statement
does not concern arbitrary subgroups, including full subdirect subgroups. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G H : Type*} [Group G] [Group H]

/-- The source containment transports along the same onto map as the
two actual characteristic subgroups. No group-order premise is needed. -/
theorem primeEvaluationKernel_le_commutator_of_surjective
    (β : G →* H) (hβ : Function.Surjective β)
    (hG : (primeAbelianizationGroupMap p G).ker ≤ commutator G) :
    (primeAbelianizationGroupMap p H).ker ≤ commutator H := by
  rw [← primeAbelianizationGroupMap_ker_map p β hβ]
  have hcomm : (commutator G).map β = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hβ, ← commutator_def]
  exact (Subgroup.map_mono hG).trans_eq hcomm

/-- Exact original-source equality is preserved by every epimorphism. -/
theorem primeEvaluationKernel_eq_commutator_of_surjective
    (β : G →* H) (hβ : Function.Surjective β)
    (hG : (primeAbelianizationGroupMap p G).ker = commutator G) :
    (primeAbelianizationGroupMap p H).ker = commutator H := by
  rw [← primeAbelianizationGroupMap_ker_map p β hβ, hG,
    map_commutator_eq, MonoidHom.range_eq_top.mpr hβ, ← commutator_def]

/-- Every normal quotient here is the literal quotient of the original G. -/
theorem primeEvaluationKernel_quotient_le_commutator
    (N : Subgroup G) [N.Normal]
    (hG : (primeAbelianizationGroupMap p G).ker ≤ commutator G) :
    (primeAbelianizationGroupMap p (G ⧸ N)).ker ≤ commutator (G ⧸ N) :=
  primeEvaluationKernel_le_commutator_of_surjective p
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hG

theorem primeEvaluationKernel_quotient_eq_commutator
    (N : Subgroup G) [N.Normal]
    (hG : (primeAbelianizationGroupMap p G).ker = commutator G) :
    (primeAbelianizationGroupMap p (G ⧸ N)).ker = commutator (G ⧸ N) :=
  primeEvaluationKernel_eq_commutator_of_surjective p
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hG

end SymmetricSubgroupAsymptotics
