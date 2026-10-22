import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent

/-! The original upper symmetric shears, including each coordinate
long-root word, belong to the actual defining-characteristic U. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGMatrixShearUnits

theorem flag_pos_lt_neg (n : ℕ) (i j : Fin n) :
    flagEquiv n (Sum.inl i) < flagEquiv n (Sum.inr j) := by
  change i.val < n + (Fin.rev j).val
  have hi := i.isLt
  omega

theorem upperShear_triangular (K : Type) [Field K] (n : ℕ)
    (S : Matrix (Fin n) (Fin n) K) :
    (upper S : Mat K n).BlockTriangular (flagEquiv n) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hij : i ≠ j := by intro h; subst j; exact (lt_irrefl _ hxy)
      change (1 : Matrix (Fin n) (Fin n) K) i j = 0
      exact Matrix.one_apply_ne hij
    | inr j =>
      exact False.elim ((not_lt_of_gt (flag_pos_lt_neg n i j)) hxy)
  | inr i =>
    cases y with
    | inl j => rfl
    | inr j =>
      have hij : i ≠ j := by intro h; subst j; exact (lt_irrefl _ hxy)
      change (1 : Matrix (Fin n) (Fin n) K) i j = 0
      exact Matrix.one_apply_ne hij

theorem upperShear_mem_unipotent (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (S : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hS : S.IsSymm) :
    (⟨upper S, symmetric_upper_mem K r hr S hS⟩ : elementaryRootGroup K (r + 1)) ∈
      unipotent K (r + 1) := by
  refine ⟨upperShear_triangular K (r + 1) S, ?_⟩
  intro i
  cases i <;> exact Matrix.one_apply_eq _

def upperShearInU (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (S : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hS : S.IsSymm) : unipotent K (r + 1) :=
  ⟨⟨upper S, symmetric_upper_mem K r hr S hS⟩, upperShear_mem_unipotent K r hr S hS⟩

theorem unipotent_lower_left_zero (K : Type) [Field K] (n : ℕ) (g : unipotent K n)
    (i j : Fin n) : (g.val.val : Mat K n) (Sum.inr i) (Sum.inl j) = 0 :=
  g.property.1 (flag_pos_lt_neg n j i)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
