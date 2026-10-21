import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapeCoverage
import Mathlib.Data.Finset.Lattice.Fold

/-! Finite joins of actual atom subgroups form a closed low-row family.
An actual seed-normalizing conjugator which permutes the atoms preserves
this family. No assertion that a displayed finite family is exhaustive
is assumed here. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.FiniteSeedAtomJoinRows

variable {G I : Type*} [Group G]

def rows (H : Subgroup G) (atoms : I → Subgroup G) (s : Finset I) : Subgroup G :=
  H ⊔ s.sup atoms

theorem seed_le (H : Subgroup G) (atoms : I → Subgroup G) (s : Finset I) :
    H ≤ rows H atoms s := le_sup_left

theorem empty (H : Subgroup G) (atoms : I → Subgroup G) :
    rows H atoms ∅ = H := by
  simp only [rows, Finset.sup_empty, sup_bot_eq]

theorem union [DecidableEq I] (H : Subgroup G) (atoms : I → Subgroup G)
    (s t : Finset I) : rows H atoms s ⊔ rows H atoms t = rows H atoms (s ∪ t) := by
  simp only [rows, Finset.sup_union]
  rw [sup_sup_sup_comm, sup_idem]

theorem conjugate_finset_sup (c : G) (atoms : I → Subgroup G) (s : Finset I) :
    MulAut.conj c • s.sup atoms = s.sup (fun i => MulAut.conj c • atoms i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sup_empty, Subgroup.smul_bot]
  · intro i t _ ih
    simp only [Finset.sup_insert, Subgroup.smul_sup, ih]

theorem conjugated [DecidableEq I] (H : Subgroup G) (atoms : I → Subgroup G)
    (c : G) (σ : I → I) (hH : MulAut.conj c • H = H)
    (hAtoms : ∀ i, MulAut.conj c • atoms i = atoms (σ i)) (s : Finset I) :
    MulAut.conj c • rows H atoms s = rows H atoms (s.image σ) := by
  unfold rows
  rw [Subgroup.smul_sup, hH, conjugate_finset_sup, Finset.sup_image]
  apply congrArg (fun V : Subgroup G => H ⊔ V)
  apply Finset.sup_congr rfl
  intro i _
  exact hAtoms i

end SymmetricSubgroupAsymptotics.FiniteSeedAtomJoinRows

end
