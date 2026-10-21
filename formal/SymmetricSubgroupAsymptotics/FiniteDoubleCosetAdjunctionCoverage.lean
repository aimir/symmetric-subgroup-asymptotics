import SymmetricSubgroupAsymptotics.FiniteLeftCosetAdjunctionCoverage

/-! A finite forest of actual left/right subgroup factors compresses the
coset adjunction checks to double-coset roots. No normality or subgroup
classification assumption is involved. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] (H : Subgroup G)

theorem adjoin_eq_of_same_right_coset (x y : G) (hxy : x⁻¹ * y ∈ H) :
    H ⊔ Subgroup.closure {x} = H ⊔ Subgroup.closure {y} := by
  have h := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) x⁻¹ y⁻¹ (by simpa only [inv_inv] using hxy)
  simpa only [Subgroup.closure_singleton_inv] using h

structure FiniteDoubleCosetAdjunctionReduction {q : ℕ}
    (representatives : Fin q → G) (r : ℕ) where
  roots : Fin r → Fin q
  label : Fin q → Fin r
  rank : Fin q → ℕ
  parent : ∀ i, i ≠ roots (label i) → Fin q
  factor : ∀ i, i ≠ roots (label i) → G
  factor_mem : ∀ i hi, factor i hi ∈ H
  residue_mem : ∀ i hi,
    representatives (parent i hi) * factor i hi * (representatives i)⁻¹ ∈ H
  parent_lt : ∀ i hi, rank (parent i hi) < rank i
  parent_label : ∀ i hi, label (parent i hi) = label i

namespace FiniteDoubleCosetAdjunctionReduction

variable {H} {q r : ℕ} {representatives : Fin q → G}
  (D : FiniteDoubleCosetAdjunctionReduction H representatives r)

theorem adjoin_eq_root (i : Fin q) :
    H ⊔ Subgroup.closure {representatives i} =
      H ⊔ Subgroup.closure {representatives (D.roots (D.label i))} := by
  by_cases hi : i = D.roots (D.label i)
  · exact congrArg (fun j => H ⊔ Subgroup.closure {representatives j}) hi
  · have hleft := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset (H := H)
      (representatives (D.parent i hi) * D.factor i hi) (representatives i)
      (D.residue_mem i hi)
    have hright := adjoin_eq_of_same_right_coset H
      (representatives (D.parent i hi))
      (representatives (D.parent i hi) * D.factor i hi)
      (by simpa only [inv_mul_cancel_left] using D.factor_mem i hi)
    calc
      _ = H ⊔ Subgroup.closure
          {representatives (D.parent i hi) * D.factor i hi} := hleft.symm
      _ = H ⊔ Subgroup.closure {representatives (D.parent i hi)} := hright.symm
      _ = H ⊔ Subgroup.closure {representatives (D.roots (D.label (D.parent i hi)))} :=
        adjoin_eq_root (D.parent i hi)
      _ = _ := by rw [D.parent_label i hi]
termination_by D.rank i
decreasing_by exact D.parent_lt i hi

theorem covered_representative {J : Type*} (rows : J → Subgroup G)
    (hroot : ∀ k : Fin r, FiniteSubgroupAdjunctionCoverage.Covered rows
      (H ⊔ Subgroup.closure {representatives (D.roots k)})) (i : Fin q) :
    FiniteSubgroupAdjunctionCoverage.Covered rows
      (H ⊔ Subgroup.closure {representatives i}) := by
  rw [D.adjoin_eq_root i]
  exact hroot _

end FiniteDoubleCosetAdjunctionReduction
end SymmetricSubgroupAsymptotics

end
