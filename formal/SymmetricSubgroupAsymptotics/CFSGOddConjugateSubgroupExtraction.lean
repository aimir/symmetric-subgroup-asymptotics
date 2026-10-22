import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! If a subgroup contains an involution inverting an odd-order element,
the subgroup together with its conjugate by that element already contains
the element. Thus explicit ordinary generation by the element and the
subgroup becomes generation by two actual conjugate subgroups. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOddConjugateSubgroupExtraction

theorem odd_element_mem_two_conjugates {G : Type*} [Group G]
    (P : Subgroup G) (p g : G) (n : ℕ) (hpP : p ∈ P)
    (hp : p ^ 2 = 1) (hinv : p * g * p⁻¹ = g⁻¹)
    (hg : g ^ (2 * n + 1) = 1) :
    g ∈ Subgroup.closure ((P : Set G) ∪ P.map (MulAut.conj g).toMonoidHom) := by
  let K := Subgroup.closure ((P : Set G) ∪ P.map (MulAut.conj g).toMonoidHom)
  have hpK : p ∈ K := Subgroup.subset_closure (Or.inl hpP)
  have hconj : g * p * g⁻¹ ∈ K :=
    Subgroup.subset_closure (Or.inr ⟨p, hpP, rfl⟩)
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
  have he : p * (g * p * g⁻¹) = (g * g)⁻¹ := by
    calc
      p * (g * p * g⁻¹) = (p * g * p⁻¹) * g⁻¹ := by rw [hpi]; group
      _ = g⁻¹ * g⁻¹ := by rw [hinv]
      _ = (g * g)⁻¹ := by rw [mul_inv_rev]
  have hs : g ^ 2 ∈ K := by
    have h := K.inv_mem (K.mul_mem hpK hconj)
    rw [he, inv_inv, ← pow_two] at h
    exact h
  have hpower : (g ^ 2) ^ (n + 1) = g := by
    calc
      (g ^ 2) ^ (n + 1) = g ^ (2 * (n + 1)) := by rw [pow_mul]
      _ = g ^ ((2 * n + 1) + 1) := by congr 1
      _ = g ^ (2 * n + 1) * g := by rw [pow_succ]
      _ = g := by rw [hg, one_mul]
  have hm := K.pow_mem hs (n + 1)
  change g ∈ K
  simpa only [hpower] using hm

end SymmetricSubgroupAsymptotics.CFSGOddConjugateSubgroupExtraction
