import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! An actual nonzero square-zero operator on a three-dimensional space
has a literal basis consisting of one length-two chain and one kernel
vector. All statements hold over arbitrary fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteThreeSquareZeroBasis

open Module
open scoped BigOperators Matrix
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

theorem range_finrank_eq_one (N : Module.End K V) (hd : Module.finrank K V = 3)
    (hsq : ∀ x : V, N (N x) = 0) (hne : N ≠ 0) :
    Module.finrank K N.range = 1 := by
  have hle : N.range ≤ N.ker := by
    rintro x ⟨y, rfl⟩
    exact hsq y
  have hm := Submodule.finrank_mono hle
  have hs := N.finrank_range_add_finrank_ker
  have hp : 1 ≤ Module.finrank K N.range :=
    Submodule.one_le_finrank_iff.mpr (fun h => hne (LinearMap.range_eq_bot.mp h))
  omega

theorem exists_basis (N : Module.End K V) (hd : Module.finrank K V = 3)
    (hsq : ∀ x : V, N (N x) = 0) (hne : N ≠ 0) :
    ∃ b : Basis (Fin 3) K V,
      N (b 0) = b 1 ∧ N (b 1) = 0 ∧ N (b 2) = 0 := by
  classical
  have hr := range_finrank_eq_one N hd hsq hne
  have hk : Module.finrank K N.ker = 2 := by
    have hh := N.finrank_range_add_finrank_ker
    omega
  obtain ⟨v, hv⟩ : ∃ v : V, N v ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  let w : N.ker := ⟨N v, hsq v⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  obtain ⟨u, hu⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (by omega : 1 < Module.finrank K N.ker) hw
  have hu0 : N (u : V) = 0 := u.property
  have hi : LinearIndependent K ![v, N v, (u : V)] := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hrel : c 0 • v + c 1 • N v + c 2 • (u : V) = 0 := by
      simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] using hc
    have hNrel : c 0 • N v = 0 := by
      have hh := congrArg N hrel
      simpa only [map_add, map_smul, hsq v, hu0, smul_zero, add_zero, map_zero] using hh
    have hc0 : c 0 = 0 := (smul_eq_zero.mp hNrel).resolve_right hv
    have hker : c 1 • w + c 2 • u = 0 := by
      apply Subtype.ext
      change c 1 • N v + c 2 • (u : V) = 0
      simpa only [hc0, zero_smul, zero_add] using hrel
    obtain ⟨hc1, hc2⟩ := LinearIndependent.pair_iff.mp hu _ _ hker
    intro i
    fin_cases i <;> simp_all
  let b := basisOfLinearIndependentOfCardEqFinrank' ![v, N v, (u : V)] hi
    (by simpa only [Fintype.card_fin] using hd.symm)
  refine ⟨b, ?_, ?_, ?_⟩ <;>
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]
  · exact hsq v
  · exact hu0

theorem exists_shifted_basis (A : Module.End K V) (a : K)
    (hd : Module.finrank K V = 3) (hsq : (A - a • 1) * (A - a • 1) = 0)
    (hne : A ≠ a • 1) :
    ∃ b : Basis (Fin 3) K V,
      A (b 0) = a • b 0 + b 1 ∧ A (b 1) = a • b 1 ∧ A (b 2) = a • b 2 := by
  let N : Module.End K V := A - a • 1
  have hN : ∀ x : V, N (N x) = 0 := by
    intro x
    exact DFunLike.congr_fun hsq x
  have hN0 : N ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨b, h01, h1, h2⟩ := exists_basis N hd hN hN0
  have h01' : A (b 0) - a • b 0 = b 1 := h01
  have h1' : A (b 1) - a • b 1 = 0 := h1
  have h2' : A (b 2) - a • b 2 = 0 := h2
  exact ⟨b, sub_eq_iff_eq_add'.mp h01', sub_eq_zero.mp h1', sub_eq_zero.mp h2'⟩

end SymmetricSubgroupAsymptotics.FiniteThreeSquareZeroBasis
