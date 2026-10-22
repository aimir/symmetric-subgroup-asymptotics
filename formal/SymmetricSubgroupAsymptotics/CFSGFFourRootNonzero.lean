import SymmetricSubgroupAsymptotics.CFSGFFourSerreCartanRelations
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries

/-! A literal coefficient-one entry makes every folded F4 positive root
nonzero. This supplies genuine sl2 triples for the finite-dimensional
Serre-power argument, with no root-faithfulness hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckColumns
local instance fFourRootNonzeroDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem e6E_selected_entry (i j : Fin 6) :
    e6E i (.inl (E6Index j))
      (.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index j)))=
      if j=i then 1 else 0 := by
  change RootPairing.GeckConstruction.e (E6Index i) _ _=_
  rw [CFSGNormTwoGeckNormalizedEntries.E_inl_inr CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base (E6Index i) (E6Index j)]
  by_cases h : j=i
  · subst j
    simp
  · simp [h,E6Index.injective.ne h]

theorem positive_selected_entry (i : Fin 4) :
    positive i (.inl (E6Index (representative i)))
      (.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        (E6Index (representative i))))=1 := by
  fin_cases i <;> norm_num [positive,representative,Matrix.add_apply,e6E_selected_entry] <;> decide

theorem positive_ne_zero (i : Fin 4) : positive i≠0 := by
  intro h
  have hh := congrArg (fun M : Mat=>M (.inl (E6Index (representative i)))
    (.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      (E6Index (representative i))))) h
  dsimp only at hh
  rw [positive_selected_entry,Matrix.zero_apply] at hh
  exact one_ne_zero hh

theorem cartan_ne_zero (i : Fin 4) : cartan i≠0 := by
  intro h
  have hh := HE i i
  rw [h,zero_lie,CartanMatrix.F₄_diag] at hh
  have he : (2:ℚ) • positive i=0 := by
    simpa only [two_smul] using hh.symm
  exact positive_ne_zero i ((smul_eq_zero.mp he).resolve_left (by norm_num))

def sl2Triple (i : Fin 4) : IsSl2Triple (cartan i) (positive i) (negative i) where
  h_ne_zero := cartan_ne_zero i
  lie_e_f := by simpa only [if_pos rfl] using EF i i
  lie_h_e_nsmul := by simpa only [CartanMatrix.F₄_diag,two_smul] using HE i i
  lie_h_f_nsmul := by simpa only [CartanMatrix.F₄_diag,two_smul] using HF i i

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
