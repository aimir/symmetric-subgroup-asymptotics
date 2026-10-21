import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder
import SymmetricSubgroupAsymptotics.CFSGJ4Generation
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Mathieu22
import Mathlib.Tactic.FinCases

/-! Further literal even-order witnesses: the three-generator J4
presentation and the actual 22-point permutation construction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

private theorem even_of_nontrivial_involution {G : Type*} [Group G]
    (x : G) (hs : x ^ 2 = 1) (hne : x ≠ 1) : Even (Nat.card G) := by
  by_contra heven
  exact hne (eq_one_of_square_eq_one_of_odd_card (Nat.not_even_iff_odd.mp heven) x hs)

theorem j4t_sq : j4t ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ CFSG.Models.Presentations.J4.relators})
    (x := (FreeGroup.of (2 : Fin 3)) ^ 2)
    (by
      change _ ∈ CFSG.Models.Presentations.J4.relators
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))))))
  simpa only [map_pow, PresentedGroup.of] using h

theorem j4_even_card
    (hn : ¬ IsMulCommutative CFSG.Models.Presentations.J4.Model) :
    Even (Nat.card CFSG.Models.Presentations.J4.Model) := by
  apply even_card_of_involutions_and_one_generator
    (PresentedGroup.of (rels := {w | w ∈ CFSG.Models.Presentations.J4.relators}))
    (1 : Fin 3) (PresentedGroup.closure_range_of _)
  · intro i hi
    fin_cases i
    · exact j4x_sq
    · exact (hi rfl).elim
    · exact j4t_sq
  · exact hn

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem mathieu22_b_pow_eight : CFSG.Models.Mathieu22Construction.b ^ 8 = 1 := by
  ext i
  fin_cases i <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem mathieu22_b_pow_four_ne : CFSG.Models.Mathieu22Construction.b ^ 4 ≠ 1 := by
  intro h
  have he := congrArg (fun g : Equiv.Perm (Fin 22) => g 0) h
  have hne : (CFSG.Models.Mathieu22Construction.b ^ 4) 0 ≠ (0 : Fin 22) := by decide
  exact hne he

private def mathieu22B : CFSG.Models.Mathieu22 :=
  ⟨CFSG.Models.Mathieu22Construction.b, Subgroup.subset_closure (Or.inr rfl)⟩

private theorem mathieu22B_eighth : mathieu22B ^ 8 = 1 := by
  apply Subtype.ext
  exact mathieu22_b_pow_eight

private theorem mathieu22B_fourth_ne : mathieu22B ^ 4 ≠ 1 := by
  intro h
  have hv := congrArg (fun g : CFSG.Models.Mathieu22 => g.val) h
  change mathieu22B.val ^ 4 = 1 at hv
  rw [show mathieu22B.val = CFSG.Models.Mathieu22Construction.b from rfl] at hv
  exact mathieu22_b_pow_four_ne hv

theorem mathieu22_even_card : Even (Nat.card CFSG.Models.Mathieu22) := by
  apply even_of_nontrivial_involution (mathieu22B ^ 4)
  · simpa only [← pow_mul] using mathieu22B_eighth
  · exact mathieu22B_fourth_ne

end SymmetricSubgroupAsymptotics.CFSGReduction
