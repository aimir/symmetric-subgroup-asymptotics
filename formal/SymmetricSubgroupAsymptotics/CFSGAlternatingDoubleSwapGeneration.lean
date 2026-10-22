import SymmetricSubgroupAsymptotics.CFSGPermutationCrossSwapWords
import SymmetricSubgroupAsymptotics.NaturalAlternatingChief
import Mathlib.Tactic.FinCases

/-! Two double transpositions whose supports meet in exactly one point
produce an adjacent three-cycle. Together with a full odd rotation this
gives the actual alternating group by the proved normal-subgroup bridge. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingDoubleSwapGeneration
open CFSGPermutationCrossSwapWords

variable {X : Type} [DecidableEq X]

theorem overlap_square (f : Fin 7 → X) (hf : Function.Injective f) :
    (doubleSwap (f 3) (f 4) (f 5) (f 6) *
      doubleSwap (f 0) (f 1) (f 2) (f 3)) ^ 2 =
      Equiv.swap (f 2) (f 3) * Equiv.swap (f 3) (f 4) := by
  ext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hf.eq_iff]
  · have hn : ∀ i : Fin 7, x ≠ f i := fun i h => hx ⟨i, h.symm⟩
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hn]

theorem conjugate_doubleSwap (g : Equiv.Perm X) (a b c d : X) :
    g * doubleSwap a b c d * g⁻¹ = doubleSwap (g a) (g b) (g c) (g d) := by
  change (MulAut.conj g) (Equiv.swap a b * Equiv.swap c d) = _
  rw [map_mul]
  change (g * Equiv.swap a b * g⁻¹) * (g * Equiv.swap c d * g⁻¹) = _
  rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply]
  rfl

/-- The seven coordinates are literal distinct points of the same action.
The translated double swap is not introduced as an independent generator. -/
theorem alternating_le_of_cycle_doubleSwap [Fintype X]
    (G : Subgroup (Equiv.Perm X)) (g : Equiv.Perm X)
    (f : Fin 7 → X) (hf : Function.Injective f)
    (hsize : 5 ≤ Nat.card X) (hcycle : g.IsCycle)
    (hsupport : g.support = Finset.univ) (heven : g ∈ alternatingGroup X)
    (hg : g ∈ G) (ha : doubleSwap (f 0) (f 1) (f 2) (f 3) ∈ G)
    (hshift : ∀ i : Fin 4,
      (g ^ 3) (f ⟨i.val, by omega⟩) = f ⟨i.val + 3, by omega⟩)
    (h23 : g (f 2) = f 3) (h34 : g (f 3) = f 4) :
    alternatingGroup X ≤ G := by
  have hb : doubleSwap (f 3) (f 4) (f 5) (f 6) ∈ G := by
    have hs0 : (g ^ 3) (f 0) = f 3 := by simpa using hshift (0 : Fin 4)
    have hs1 : (g ^ 3) (f 1) = f 4 := by simpa using hshift (1 : Fin 4)
    have hs2 : (g ^ 3) (f 2) = f 5 := by simpa using hshift (2 : Fin 4)
    have hs3 : (g ^ 3) (f 3) = f 6 := by simpa using hshift (3 : Fin 4)
    have h := G.mul_mem (G.mul_mem (G.pow_mem hg 3) ha) (G.inv_mem (G.pow_mem hg 3))
    rw [conjugate_doubleSwap] at h
    simpa only [hs0, hs1, hs2, hs3] using h
  have ht : Equiv.swap (f 2) (f 3) * Equiv.swap (f 3) (f 4) ∈ G := by
    have h := G.pow_mem (G.mul_mem hb ha) 2
    rwa [overlap_square f hf] at h
  have hclosure : Subgroup.closure
      ({g, Equiv.swap (f 2) (f 3) * Equiv.swap (f 3) (f 4)} :
        Set (Equiv.Perm X)) = alternatingGroup X := by
    apply evenPairClosure_eq_alternating hsize g (Equiv.swap (f 3) (f 4)) _
      (Equiv.swap_inv _ _)
    · simpa only [h34] using Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupport (f 3)
    · exact heven
    · exact hcycle.ne_one
    · exact Or.inl (cycle_adjacent_commutator g (f 2) (f 3) (f 4) h23 h34)
  rw [← hclosure]
  exact (Subgroup.closure_le _).mpr (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hg
    · exact ht)

end SymmetricSubgroupAsymptotics.CFSGAlternatingDoubleSwapGeneration
