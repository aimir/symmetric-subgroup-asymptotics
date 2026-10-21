import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Distinct actual nonzero leading coordinates give independent original
vectors. No leading monomial is substituted for its actual lower terms. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M] {n : ℕ}

theorem linearIndependent_of_distinct_leading
    (s : Finset (Fin n)) (v : s → M) (C : M →ₗ[k] (Fin n → k))
    (hlead : ∀ a : s, HasLeading (C (v a)) a.val) :
    LinearIndependent k v := by
  apply linearIndependent_iff'.mpr
  intro t g hsum i hi
  by_contra hgi
  let active := t.filter (fun j => g j ≠ 0)
  have hactive : active.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  let m := active.max' hactive
  have hm : m ∈ active := active.max'_mem hactive
  have hmt : m ∈ t := (Finset.mem_filter.mp hm).1
  have hgm : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hterm (j : s) (hjt : j ∈ t) (hne : j ≠ m) :
      g j * C (v j) m.val = 0 := by
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hja : j ∈ active := Finset.mem_filter.mpr ⟨hjt, hgj⟩
      have hjm : j < m := lt_of_le_of_ne (active.le_max' j hja) hne
      rw [(hlead j).2 m.val hjm, mul_zero]
  have he := congrArg (fun x : M => C x m.val) hsum
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_zero, Pi.zero_apply] at he
  have hsingle : (∑ j ∈ t, g j * C (v j) m.val) = g m * C (v m) m.val :=
    Finset.sum_eq_single m hterm (fun hn => False.elim (hn hmt))
  rw [hsingle] at he
  exact (mul_ne_zero hgm (hlead m).1) he

theorem card_le_finrank_of_actual_leading_vectors [FiniteDimensional k M]
    (s : Finset (Fin n)) (C : M →ₗ[k] (Fin n → k))
    (hactual : ∀ a ∈ s, ∃ v : M, HasLeading (C v) a) :
    s.card ≤ Module.finrank k M := by
  let v : s → M := fun a => Classical.choose (hactual a.val a.property)
  have hv : ∀ a : s, HasLeading (C (v a)) a.val := fun a =>
    Classical.choose_spec (hactual a.val a.property)
  have hi := linearIndependent_of_distinct_leading s v C hv
  simpa only [Fintype.card_coe] using hi.fintype_card_le_finrank

end SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
