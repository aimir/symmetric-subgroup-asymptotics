import SymmetricSubgroupAsymptotics.FiniteDoubleCosetAdjunctionCoverage

/-! Compression of seed-adjunction checks by actual seed-normalizing
point conjugators as well as subgroup factors. The finite forest records
and proves every normalizer and residue equation; no normalizer class list
or ambient normalizer identification is an input. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

namespace FiniteSubgroupAdjunctionCoverage

theorem covered_conjugate {I : Type*} (rows : I → Subgroup G)
    {U : Subgroup G} (hU : Covered rows U) (c : G) :
    Covered rows (MulAut.conj c • U) := by
  obtain ⟨i, d, hd⟩ := hU
  refine ⟨i, d * c⁻¹, ?_⟩
  rw [map_mul, mul_smul, map_inv, inv_smul_smul, hd]

end FiniteSubgroupAdjunctionCoverage

structure FiniteNormalizerAdjunctionReduction (H : Subgroup G) {q : ℕ}
    (representatives : Fin q → G) (r : ℕ) where
  roots : Fin r → Fin q
  label : Fin q → Fin r
  rank : Fin q → ℕ
  parent : ∀ i, i ≠ roots (label i) → Fin q
  conjugator : ∀ i, i ≠ roots (label i) → G
  conjugates_seed : ∀ i hi, MulAut.conj (conjugator i hi) • H = H
  factor : ∀ i, i ≠ roots (label i) → G
  factor_mem : ∀ i hi, factor i hi ∈ H
  residue_mem : ∀ i hi,
    (MulAut.conj (conjugator i hi)) (representatives (parent i hi)) * factor i hi *
      (representatives i)⁻¹ ∈ H
  parent_lt : ∀ i hi, rank (parent i hi) < rank i

namespace FiniteNormalizerAdjunctionReduction

variable {H : Subgroup G} {q r : ℕ} {representatives : Fin q → G}
  (D : FiniteNormalizerAdjunctionReduction H representatives r)

theorem edge_conjugated (i : Fin q) (hi : i ≠ D.roots (D.label i)) :
    MulAut.conj (D.conjugator i hi) •
      (H ⊔ Subgroup.closure {representatives (D.parent i hi)}) =
        H ⊔ Subgroup.closure {representatives i} := by
  rw [Subgroup.smul_sup, D.conjugates_seed i hi, Subgroup.smul_closure,
    Set.smul_set_singleton]
  change H ⊔ Subgroup.closure
      {(MulAut.conj (D.conjugator i hi)) (representatives (D.parent i hi))} = _
  have hright := adjoin_eq_of_same_right_coset H
    ((MulAut.conj (D.conjugator i hi)) (representatives (D.parent i hi)))
    ((MulAut.conj (D.conjugator i hi)) (representatives (D.parent i hi)) * D.factor i hi)
    (by simpa only [inv_mul_cancel_left] using D.factor_mem i hi)
  exact hright.trans (FiniteLeftCosetCover.adjoin_eq_of_same_left_coset (H := H)
    ((MulAut.conj (D.conjugator i hi)) (representatives (D.parent i hi)) * D.factor i hi)
    (representatives i) (D.residue_mem i hi))

theorem covered_representative {I : Type*} (rows : I → Subgroup G)
    (hroot : ∀ k : Fin r, FiniteSubgroupAdjunctionCoverage.Covered rows
      (H ⊔ Subgroup.closure {representatives (D.roots k)})) (i : Fin q) :
    FiniteSubgroupAdjunctionCoverage.Covered rows
      (H ⊔ Subgroup.closure {representatives i}) := by
  by_cases hi : i = D.roots (D.label i)
  · rw [hi]
    exact hroot _
  · rw [← D.edge_conjugated i hi]
    exact FiniteSubgroupAdjunctionCoverage.covered_conjugate rows
      (covered_representative rows hroot (D.parent i hi)) (D.conjugator i hi)
termination_by D.rank i
decreasing_by exact D.parent_lt i hi

end FiniteNormalizerAdjunctionReduction
end SymmetricSubgroupAsymptotics

end
