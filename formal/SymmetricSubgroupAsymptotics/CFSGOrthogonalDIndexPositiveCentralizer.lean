import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays
import Mathlib.Data.Fintype.Card

/-! Sparse positive-root centralizer algebra for actual D matrices.
Commuting with all paired alternating upper directions already forces
both diagonal blocks of a unit-diagonal upper matrix to be identity.
Unlike the C argument, no diagonal long-root direction is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveCentralizer
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

def pairedUpper {r : ℕ} (i j : Fin r) : Mat K r :=
  Matrix.single (Sum.inl i) (Sum.inr j) 1 - Matrix.single (Sum.inl j) (Sum.inr i) 1

private theorem exists_third (s : ℕ) (i j : Fin (s + 4)) :
    ∃ k : Fin (s + 4), k ≠ i ∧ k ≠ j := by
  have hc : ({i, j} : Finset (Fin (s + 4))).card < (Finset.univ : Finset (Fin (s + 4))).card := by
    have h := (Finset.card_le_two : ({i, j} : Finset (Fin (s + 4))).card ≤ 2)
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk⟩

theorem upper_of_paired_commutation (s : ℕ) (A : Mat K (s + 4))
    (hL : ∀ i j, A (Sum.inr i) (Sum.inl j) = 0)
    (hdiag : ∀ i, A i i = 1)
    (hcomm : ∀ i j : Fin (s + 4), i ≠ j → A * pairedUpper K i j = pairedUpper K i j * A) :
    A = Matrix.fromBlocks 1 (A.submatrix Sum.inl Sum.inr) 0 1 := by
  have hpos (k i : Fin (s + 4)) (hki : k ≠ i) : A (Sum.inl k) (Sum.inl i) = 0 := by
    obtain ⟨j, hji, hjk⟩ := exists_third s i k
    have he := congrArg (fun M : Mat K (s + 4) => M (Sum.inl k) (Sum.inr j))
      (hcomm i j (Ne.symm hji))
    dsimp only at he
    simpa [pairedUpper, Matrix.mul_apply, Matrix.single_apply, Fintype.sum_sum_type,
      hki, Ne.symm hki, hji, Ne.symm hji, hjk, Ne.symm hjk] using he
  have hneg (i j : Fin (s + 4)) (hij : i ≠ j) : A (Sum.inr i) (Sum.inr j) = 0 := by
    obtain ⟨k, hki, hkj⟩ := exists_third s i j
    have he := congrArg (fun M : Mat K (s + 4) => M (Sum.inl k) (Sum.inr j))
      (hcomm k i hki)
    dsimp only at he
    simpa [pairedUpper, Matrix.mul_apply, Matrix.single_apply, Fintype.sum_sum_type,
      hij, Ne.symm hij, hki, Ne.symm hki, hkj, Ne.symm hkj] using he.symm
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq] using hdiag (Sum.inl i)
      · simpa only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, if_neg hij] using hpos i j hij
    | inr j => rfl
  | inr i =>
    cases y with
    | inl j => exact hL i j
    | inr j =>
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq] using hdiag (Sum.inr i)
      · simpa only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_neg hij] using hneg i j hij

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveCentralizer
