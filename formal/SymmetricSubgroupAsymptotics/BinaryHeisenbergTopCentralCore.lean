import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads

/-! Every nontrivial actual normal in the original Heisenberg top contains
its specified central involution. The certificate tests only32 original
top rows and their commutators with the five original generators. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergTopCentralCore
open BinaryHeisenbergEightNaturalHeads

def z : H := generators 0
def PointEq (g h : H) : Prop := ∀ x : Fin 8, g.val x = h.val x
instance (g h : H) : Decidable (PointEq g h) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, g.val x = h.val x))

theorem eq_of_pointEq {g h : H} (hh : PointEq g h) : g = h :=
  Subtype.ext (Equiv.ext hh)

theorem z_ne_one : z ≠ 1 := by
  intro h
  have hc : ¬ PointEq z 1 := by decide +kernel
  exact hc (fun x => congrArg (fun g : H => g.val x) h)

private theorem row_cases : ∀ i : Fin 32,
    PointEq (BinaryEightOriginalRowActions.heisenbergRow i) 1 ∨
    PointEq (BinaryEightOriginalRowActions.heisenbergRow i) z ∨
    ∃ j : Fin 5, PointEq
      ⁅BinaryEightOriginalRowActions.heisenbergRow i, generators j⁆ z := by
  decide +kernel

theorem central_cases (g : H) (hg : g ∈ Subgroup.center H) : g = 1 ∨ g = z := by
  obtain ⟨i, rfl⟩ := BinaryEightOriginalRowActions.heisenbergRow_bijective.2 g
  rcases row_cases i with h | h | ⟨j, h⟩
  · exact Or.inl (eq_of_pointEq h)
  · exact Or.inr (eq_of_pointEq h)
  · have hc : ⁅BinaryEightOriginalRowActions.heisenbergRow i, generators j⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hg) (generators j)).symm
    exact False.elim (z_ne_one ((eq_of_pointEq h).symm.trans hc))

theorem normal_contains_z (T : Subgroup H) [T.Normal] (hT : T ≠ ⊥) : z ∈ T := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT
  obtain ⟨i, hi⟩ := BinaryEightOriginalRowActions.heisenbergRow_bijective.2 (x : H)
  have hg : BinaryEightOriginalRowActions.heisenbergRow i ∈ T := hi.symm ▸ x.property
  have hne : BinaryEightOriginalRowActions.heisenbergRow i ≠ 1 := by
    intro h
    exact hx (Subtype.ext (hi.symm.trans h))
  rcases row_cases i with h | h | ⟨j, h⟩
  · exact False.elim (hne (eq_of_pointEq h))
  · exact eq_of_pointEq h ▸ hg
  · have hm : ⁅BinaryEightOriginalRowActions.heisenbergRow i, generators j⁆ ∈ T := by
      have hn := Subgroup.Normal.conj_mem (H := T) inferInstance
        (BinaryEightOriginalRowActions.heisenbergRow i)⁻¹ (T.inv_mem hg) (generators j)
      simpa only [commutatorElement_def, mul_assoc] using T.mul_mem hg hn
    exact eq_of_pointEq h ▸ hm

end SymmetricSubgroupAsymptotics.BinaryHeisenbergTopCentralCore
