import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGWeightedRootPGroup

/-! The actual folded D4 simple-root units generate defining-characteristic
p-subgroups. A literal D4 coordinate grading proves strict support, including
the quadratic short-root coefficient. No Sylow or normalizer claim is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositivePGroup
open CFSGGTwoSerreMatrices

def weight : Index → ℤ :=
  Sum.elim (fun i => -(i.val : ℤ)) (fun i => (i.val : ℤ) - 7)

private theorem single_strict (K : Type) [Field K] (a b : Index)
    (hab : weight b < weight a) (c : K) (x y : Index)
    (hxy : weight x ≤ weight y) : Matrix.single a b c x y = 0 := by
  apply Matrix.single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (not_lt_of_ge hxy) hab

theorem positive_strict (K : Type) [Field K] (i : Fin 2) (x y : Index)
    (hxy : weight x ≤ weight y) : positive K i x y = 0 := by
  fin_cases i
  · change positive K 0 x y = 0
    rw [positive_zero_explicit]
    simp only [Matrix.add_apply, Matrix.sub_apply]
    rw [single_strict K (pos 0) (pos 1) (by norm_num [weight, pos]) 1 x y hxy,
      single_strict K (neg 1) (neg 0) (by norm_num [weight, neg]) 1 x y hxy,
      single_strict K (pos 2) (pos 3) (by norm_num [weight, pos]) 1 x y hxy,
      single_strict K (neg 3) (neg 2) (by norm_num [weight, neg]) 1 x y hxy,
      single_strict K (pos 2) (neg 3) (by norm_num [weight, pos, neg]) 1 x y hxy,
      single_strict K (pos 3) (neg 2) (by norm_num [weight, pos, neg]) 1 x y hxy]
    ring
  · change positive K 1 x y = 0
    rw [positive_one_explicit]
    simp only [Matrix.sub_apply]
    rw [single_strict K (pos 1) (pos 2) (by norm_num [weight, pos]) 1 x y hxy,
      single_strict K (neg 2) (neg 1) (by norm_num [weight, neg]) 1 x y hxy]
    ring

theorem positiveSecond_strict (K : Type) [Field K] (i : Fin 2) (x y : Index)
    (hxy : weight x ≤ weight y) : positiveSecond K i x y = 0 := by
  by_cases hi : i = 0
  · simp only [positiveSecond, if_pos hi]
    exact single_strict K (pos 2) (neg 2) (by norm_num [weight, pos, neg]) (-1) x y hxy
  · simp only [positiveSecond, if_neg hi, Matrix.zero_apply]

def signedWeight (negativeRoot : Bool) (x : Index) : ℤ :=
  if negativeRoot then -weight x else weight x

theorem rootMatrix_strict (K : Type) [Field K] (negRoot : Bool) (i : Fin 2)
    (x y : Index) (hxy : signedWeight negRoot x ≤ signedWeight negRoot y) :
    rootMatrix K negRoot i x y = 0 := by
  cases negRoot
  · exact positive_strict K i x y hxy
  · change positive K i y x = 0
    apply positive_strict K i y x
    change -weight x ≤ -weight y at hxy
    omega

theorem rootSecond_strict (K : Type) [Field K] (negRoot : Bool) (i : Fin 2)
    (x y : Index) (hxy : signedWeight negRoot x ≤ signedWeight negRoot y) :
    rootSecond K negRoot i x y = 0 := by
  cases negRoot
  · exact positiveSecond_strict K i x y hxy
  · change positiveSecond K i y x = 0
    apply positiveSecond_strict K i y x
    change -weight x ≤ -weight y at hxy
    omega

def rootGroup (K : Type) [Field K] (negRoot : Bool) : Subgroup ((Mat K)ˣ) :=
  Subgroup.closure (Set.range (fun z : Fin 2 × K => rootTransvection K negRoot z.1 z.2))

theorem rootGroup_isPGroup (K : Type) [Field K] (negRoot : Bool)
    (p : ℕ) [Fact p.Prime] [CharP K p] : IsPGroup p (rootGroup K negRoot) := by
  apply CFSGWeightedRootPGroup.generated_isPGroup (signedWeight negRoot)
    (fun z : Fin 2 × K => rootTransvection K negRoot z.1 z.2)
  intro z
  exact CFSGWeightedRootPGroup.quadratic_identity_on_nonincreasing (signedWeight negRoot)
    (rootTransvection K negRoot z.1 z.2) (rootMatrix K negRoot z.1)
    (rootSecond K negRoot z.1) z.2 (rootTransvection_val K negRoot z.1 z.2)
    (rootMatrix_strict K negRoot z.1) (rootSecond_strict K negRoot z.1)

theorem positive_sup_negative (K : Type) [Field K] :
    rootGroup K false ⊔ rootGroup K true = naturalGroup K := by
  apply le_antisymm
  · apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨z, rfl⟩
      exact (naturalRoot K false z.1 z.2).property
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨z, rfl⟩
      exact (naturalRoot K true z.1 z.2).property
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨negRoot, i, t, rfl⟩
    cases negRoot
    · exact (show rootGroup K false ≤ rootGroup K false ⊔ rootGroup K true from le_sup_left)
        (Subgroup.subset_closure ⟨(i, t), rfl⟩)
    · exact (show rootGroup K true ≤ rootGroup K false ⊔ rootGroup K true from le_sup_right)
        (Subgroup.subset_closure ⟨(i, t), rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGGTwoPositivePGroup
