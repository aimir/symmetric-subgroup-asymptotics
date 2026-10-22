import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleKernelDimension

/-! The intersection-parity identity for three genuine maximal totally
singular subspaces. The proof computes the dimension and actual radical
of the alternating triangle form, then uses its proved even rank.
This is the substantive component-parity theorem, not an assumed
orthogonal-group classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularParity
open CFSGOrthogonalDIndexSingularTriangle CFSGOrthogonalDIndexTriangleDimensions
open CFSGOrthogonalDIndexTriangleKernelDimension CFSGOrthogonalDIndexOrthogonalLattice
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem self_orthogonal_finrank (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (r : ℕ) (hV : Module.finrank K V = 2 * r) (P : Submodule K V)
    (hP : B.orthogonal P = P) : Module.finrank K P = r := by
  have h := B.finrank_add_finrank_orthogonal' P
  rw [hP, hB.ker_eq_bot, inf_bot_eq, _root_.finrank_bot, add_zero, hV] at h
  omega

theorem even_rank_plus_intersections (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P L M : Submodule K V)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) (hL : LinearMap.BilinForm.orthogonal Q.polarBilin L = L)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M)
    (hzP : ∀ x : P, Q (x : V) = 0) (hzL : ∀ x : L, Q (x : V) = 0)
    (hzM : ∀ x : M, Q (x : V) = 0) :
    Even (r + Module.finrank K ↥(P ⊓ L) + Module.finrank K ↥(L ⊓ M) +
      Module.finrank K ↥(P ⊓ M)) := by
  have hdP := self_orthogonal_finrank Q.polarBilin hQ r hV P hP
  have hdL := self_orthogonal_finrank Q.polarBilin hQ r hV L hL
  have hdM := self_orthogonal_finrank Q.polarBilin hQ r hV M hM
  have hs := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := Q.polarBilin) (P ⊔ L ⊔ M)
  rw [total_sum_orthogonal Q.polarBilin P L M hP hL hM, LinearMap.BilinForm.Nondegenerate.ker_eq_bot hQ,
    inf_bot_eq, _root_.finrank_bot, add_zero, hV] at hs
  have ht := triangleSpace_finrank P L M
  rw [hdP, hdL, hdM] at ht
  have hk := triangle_kernel_finrank Q P L M hQ hP hL hM
  have hr := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := triangleSpace P L M) (V₂ := Module.Dual K (triangleSpace P L M))
      (triangleForm Q P L M)
  obtain ⟨a, ha⟩ := triangleForm_rank_even Q P L M hzP hzL hzM
  have heven : Module.finrank K (triangleForm Q P L M).range = a + a := ha
  have htri : Module.finrank K (triangleSpace P L M) =
      r + Module.finrank K ↥(P ⊓ L ⊓ M) := by omega
  refine ⟨a + Module.finrank K (triangleForm Q P L M).ker, ?_⟩
  calc
    r + Module.finrank K ↥(P ⊓ L) + Module.finrank K ↥(L ⊓ M) +
        Module.finrank K ↥(P ⊓ M) =
      r + (Module.finrank K ↥(P ⊓ L) + Module.finrank K ↥(L ⊓ M) +
        Module.finrank K ↥(P ⊓ M)) := by omega
    _ = r + (Module.finrank K (triangleForm Q P L M).ker +
        Module.finrank K ↥(P ⊓ L ⊓ M)) := by rw [hk]
    _ = (r + Module.finrank K ↥(P ⊓ L ⊓ M)) +
        Module.finrank K (triangleForm Q P L M).ker := by omega
    _ = Module.finrank K (triangleSpace P L M) +
        Module.finrank K (triangleForm Q P L M).ker := by rw [htri]
    _ = (Module.finrank K (triangleForm Q P L M).range +
        Module.finrank K (triangleForm Q P L M).ker) +
        Module.finrank K (triangleForm Q P L M).ker := by rw [hr]
    _ = (a + Module.finrank K (triangleForm Q P L M).ker) +
        (a + Module.finrank K (triangleForm Q P L M).ker) := by rw [heven]; omega

theorem even_three_distances (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P L M : Submodule K V)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) (hL : LinearMap.BilinForm.orthogonal Q.polarBilin L = L)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M)
    (hzP : ∀ x : P, Q (x : V) = 0) (hzL : ∀ x : L, Q (x : V) = 0)
    (hzM : ∀ x : M, Q (x : V) = 0) :
    Even ((r - Module.finrank K ↥(P ⊓ L)) + (r - Module.finrank K ↥(L ⊓ M)) +
      (r - Module.finrank K ↥(P ⊓ M))) := by
  obtain ⟨a, ha⟩ := even_rank_plus_intersections Q hQ r hV P L M hP hL hM hzP hzL hzM
  have hdP := self_orthogonal_finrank Q.polarBilin hQ r hV P hP
  have hdL := self_orthogonal_finrank Q.polarBilin hQ r hV L hL
  have hbPL : Module.finrank K ↥(P ⊓ L) ≤ r := by
    calc
      _ ≤ Module.finrank K P := Submodule.finrank_mono inf_le_left
      _ = r := hdP
  have hbLM : Module.finrank K ↥(L ⊓ M) ≤ r := by
    calc
      _ ≤ Module.finrank K L := Submodule.finrank_mono inf_le_left
      _ = r := hdL
  have hbPM : Module.finrank K ↥(P ⊓ M) ≤ r := by
    calc
      _ ≤ Module.finrank K P := Submodule.finrank_mono inf_le_left
      _ = r := hdP
  exact ⟨2 * r - a, by omega⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularParity
