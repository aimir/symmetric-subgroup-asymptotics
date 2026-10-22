import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailVectorAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm

/-! Original first-pair/tail quadratic coordinates, with no division
by two. Thus the normalization step remains valid in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexPolarForm
variable (K : Type) [Field K]

theorem pairing_first_positive (n : ℕ) (v : Index (n + 1) → K) :
    polar K (Pi.single (Sum.inl (0 : Fin (n + 1))) 1) v =
      v (Sum.inr 0) := by
  simp [polar, leftPart, rightPart, dotProduct, Pi.single_apply, ite_mul, mul_ite]

theorem splitQ_tail_of_negative_head_zero (n : ℕ) (v : Index (n + 1) → K)
    (hv : v (Sum.inr 0) = 0) :
    splitQ K v = splitQ K (tailRestriction K n v) := by
  change (∑ i : Fin (n + 1), v (Sum.inl i) * v (Sum.inr i)) =
    ∑ i : Fin n, v (Sum.inl i.succ) * v (Sum.inr i.succ)
  rw [Fin.sum_univ_succ]
  simp only [hv, mul_zero, zero_add]

theorem vector_eq_first_of_tail_zero (n : ℕ) (v : Index (n + 1) → K)
    (ht : tailRestriction K n v = 0) (hn : v (Sum.inr 0) = 0) :
    v = v (Sum.inl 0) • Pi.single (Sum.inl (0 : Fin (n + 1))) 1 := by
  funext x
  rcases x with i | i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hh := congrFun ht (Sum.inl j)
      simpa [tailRestriction, tailIndex, Pi.single_apply] using hh
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa [Pi.single_apply] using hn
    · have hh := congrFun ht (Sum.inr j)
      simpa [tailRestriction, tailIndex, Pi.single_apply] using hh

theorem tailElementaryHom_fixes_first_positive (n : ℕ) (hn : 2 ≤ n)
    (g : elementaryRootGroup K n) :
    ((tailElementaryHom K n hn g).val : Mat K (n + 1)) *ᵥ
        Pi.single (Sum.inl (0 : Fin (n + 1))) 1 =
      Pi.single (Sum.inl (0 : Fin (n + 1))) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  obtain ⟨x, rfl⟩ := (tailEquiv n).surjective x
  change tailMatrixHom K n (g.val : Mat K n) (tailEquiv n x) (tailEquiv n (Sum.inr 0)) =
    (Pi.single (tailEquiv n (Sum.inr 0)) (1 : K) : Index (n + 1) → K) (tailEquiv n x)
  rw [tailMatrixHom_apply_equiv]
  rcases x with i | j
  · have hne : tailEquiv n (Sum.inr 0) ≠ tailEquiv n (Sum.inl i) := by
      intro he
      cases (tailEquiv n).injective he
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Pi.single_apply, if_neg (Ne.symm hne)]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Pi.single_apply,
      (tailEquiv n).injective.eq_iff, Sum.inr.injEq]

theorem vector_eq_first_add_tail_basis (s : ℕ) (v : Index (s + 2) → K)
    (ht : tailRestriction K (s + 1) v = Pi.single (Sum.inl (0 : Fin (s + 1))) 1)
    (hn : v (Sum.inr 0) = 0) :
    v = v (Sum.inl 0) • Pi.single (Sum.inl (0 : Fin (s + 2))) 1 +
      Pi.single (Sum.inl (0 : Fin (s + 1)).succ) 1 := by
  funext x
  rcases x with i | i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hh := congrFun ht (Sum.inl j)
      have hsucc : j.succ = (1 : Fin (s + 2)) ↔ j = 0 := by
        change j.succ = (0 : Fin (s + 1)).succ ↔ j = 0
        exact Fin.succ_inj
      simpa [tailRestriction, tailIndex, Pi.single_apply, eq_comm, hsucc] using hh
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa [Pi.single_apply] using hn
    · have hh := congrFun ht (Sum.inr j)
      simpa [tailRestriction, tailIndex, Pi.single_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
