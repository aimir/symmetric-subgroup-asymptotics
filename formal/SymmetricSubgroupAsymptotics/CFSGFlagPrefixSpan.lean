import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
import Mathlib.LinearAlgebra.Span.Basic

/-! A coordinate flag grows by its actual next coordinate vector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFlagPrefixSpan
open CFSGMatrixFlagNormalizer
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {m : ℕ}

theorem zero_eq_bot (e : I ≃ Fin m) : flagPrefix (K := K) e 0 = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    exact funext fun i => hv i (Nat.zero_le _)
  · exact bot_le

theorem monotone (e : I ≃ Fin m) {k l : ℕ} (hkl : k ≤ l) :
    flagPrefix (K := K) e k ≤ flagPrefix (K := K) e l := by
  intro v hv i hi
  exact hv i (hkl.trans hi)

theorem single_mem_succ (e : I ≃ Fin m) (k : ℕ) (hk : k < m) :
    (Pi.single (e.symm ⟨k, hk⟩) (1 : K) : I → K) ∈ flagPrefix (K := K) e (k + 1) := by
  intro i hi
  apply Pi.single_eq_of_ne
  intro he
  subst i
  simp only [e.apply_symm_apply] at hi
  omega

theorem succ_eq_sup_single (e : I ≃ Fin m) (k : ℕ) (hk : k < m) :
    flagPrefix (K := K) e (k + 1) = flagPrefix (K := K) e k ⊔
      Submodule.span K {(Pi.single (e.symm ⟨k, hk⟩) (1 : K) : I → K)} := by
  let i := e.symm ⟨k, hk⟩
  have hei : e i = ⟨k, hk⟩ := e.apply_symm_apply _
  have hs : (Pi.single i (1 : K) : I → K) ∈ flagPrefix (K := K) e (k + 1) :=
    single_mem_succ e k hk
  apply le_antisymm
  · intro v hv
    have hw : v - v i • Pi.single i (1 : K) ∈ flagPrefix (K := K) e k := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simp
      · have hval : (e j).val ≠ k := by
          intro he
          apply hji
          apply e.injective
          apply Fin.ext
          simpa only [hei] using he
        have hvj := hv j (by omega)
        simp [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hji, hvj]
    exact Submodule.mem_sup.mpr ⟨v - v i • Pi.single i (1 : K), hw,
      v i • Pi.single i (1 : K),
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)), sub_add_cancel _ _⟩
  · apply sup_le (monotone e (Nat.le_succ k))
    exact Submodule.span_le.mpr (by simpa only [Set.singleton_subset_iff] using hs)

end SymmetricSubgroupAsymptotics.CFSGFlagPrefixSpan
