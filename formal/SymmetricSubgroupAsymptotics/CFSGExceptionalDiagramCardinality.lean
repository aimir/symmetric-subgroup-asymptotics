import SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramAutomorphisms
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite

/-! Cardinal bounds for the actual pinned exceptional diagram groups.
The checked walk invariants supply rigidity; there is no permutation census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramCardinality
open CFSGExceptionalDiagramAutomorphisms

theorem E6_evaluation_injective :
    Function.Injective (fun a : diagramGroup CartanMatrix.E₆ => a.val 0) := by
  intro a b he
  dsimp only at he
  let c : diagramGroup CartanMatrix.E₆ := b⁻¹ * a
  have hc0 : c.val 0 = 0 := by
    change b.val.symm (a.val 0) = 0
    rw [he]
    exact b.val.symm_apply_apply 0
  have hc : c = 1 := Subtype.ext (E6_fix_zero c.val c.property hc0)
  exact (inv_mul_eq_one.mp hc).symm

theorem E6_diagram_card_le : Nat.card (diagramGroup CartanMatrix.E₆) ≤ 2 := by
  classical
  let enc : diagramGroup CartanMatrix.E₆ → Fin 2 := fun a => if a.val 0 = 0 then 0 else 1
  have hinj : Function.Injective enc := by
    intro a b he
    apply E6_evaluation_injective
    by_cases ha : a.val 0 = 0
    · have hb : b.val 0 = 0 := by
        by_contra hb
        simp [enc, ha, hb] at he
      exact ha.trans hb.symm
    · have hb : b.val 0 ≠ 0 := by
        intro hb
        simp [enc, ha, hb] at he
      exact ((E6_endpoint a.val a.property).resolve_left ha).trans
        ((E6_endpoint b.val b.property).resolve_left hb).symm
  simpa using Nat.card_le_card_of_injective enc hinj

theorem E7_diagram_card_le : Nat.card (diagramGroup CartanMatrix.E₇) ≤ 1 := by
  have hinj : Function.Injective (fun _ : diagramGroup CartanMatrix.E₇ => ()) := by
    intro a b _
    apply Subtype.ext
    exact (E7_rigid a.val a.property).trans (E7_rigid b.val b.property).symm
  simpa using Nat.card_le_card_of_injective (fun _ : diagramGroup CartanMatrix.E₇ => ()) hinj

theorem E8_diagram_card_le : Nat.card (diagramGroup CartanMatrix.E₈) ≤ 1 := by
  have hinj : Function.Injective (fun _ : diagramGroup CartanMatrix.E₈ => ()) := by
    intro a b _
    apply Subtype.ext
    exact (E8_rigid a.val a.property).trans (E8_rigid b.val b.property).symm
  simpa using Nat.card_le_card_of_injective (fun _ : diagramGroup CartanMatrix.E₈ => ()) hinj

end SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramCardinality
