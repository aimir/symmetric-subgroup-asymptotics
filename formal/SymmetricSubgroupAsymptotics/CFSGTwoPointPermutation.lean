import Mathlib.GroupTheory.Perm.Basic

/-! A literal two-transposition extension of any bijection on two
specified distinct points. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGTwoPointPermutation
variable {I : Type*} [DecidableEq I]

theorem exists_map_two (a b i j : I) (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm I, σ a = i ∧ σ b = j := by
  let t := Equiv.swap a i
  let k := t b
  have hta : t a = i := Equiv.swap_apply_left a i
  have hki : k ≠ i := by
    intro he
    have ht : t b = t a := he.trans hta.symm
    exact hab (t.injective ht).symm
  refine ⟨Equiv.swap k j * t, ?_, ?_⟩
  · change Equiv.swap k j (t a) = i
    rw [hta, Equiv.swap_apply_of_ne_of_ne hki.symm hij]
  · change Equiv.swap k j k = j
    exact Equiv.swap_apply_left k j

end SymmetricSubgroupAsymptotics.CFSGTwoPointPermutation
