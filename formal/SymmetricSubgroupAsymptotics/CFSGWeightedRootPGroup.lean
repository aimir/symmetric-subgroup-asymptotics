import SymmetricSubgroupAsymptotics.CFSGFiniteWeightFlag
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups

/-! Actual units supported above a finite integer grading generate a
p-group in defining characteristic. Weight ties are handled by the
constructed complete flag and the identity diagonal blocks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGWeightedRootPGroup
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

 theorem mem_unipotent_of_weight (weight : I→ℤ) (e : I≃Fin (Fintype.card I))
    (he : ∀ i j,weight j<weight i→e i<e j) (u : (Matrix I I K)ˣ)
    (hu : ∀ i j,weight i≤weight j→(u : Matrix I I K) i j=(1 : Matrix I I K) i j) :
    u∈CFSGMatrixFlagSubgroups.unipotentUnits e := by
  constructor
  · intro i j hij
    have hne : i≠j := by intro h;subst j;exact (lt_irrefl _ hij)
    have hw : weight i≤weight j := by
      by_contra h
      have hh := he i j (lt_of_not_ge h)
      exact (not_lt_of_ge (le_of_lt hij)) hh
    rw [hu i j hw]
    simp only [Matrix.one_apply,if_neg hne]
  · intro i
    rw [hu i i le_rfl]
    exact Matrix.one_apply_eq i

theorem quadratic_identity_on_nonincreasing (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (E D : Matrix I I K) (t : K) (hval : (u : Matrix I I K)=1+t • E+t^2 • D)
    (hE : ∀ i j,weight i≤weight j→E i j=0)
    (hD : ∀ i j,weight i≤weight j→D i j=0) :
    ∀ i j,weight i≤weight j→(u : Matrix I I K) i j=(1 : Matrix I I K) i j := by
  intro i j hij
  rw [hval,Matrix.add_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.smul_apply,
    hE i j hij,hD i j hij,smul_zero,smul_zero,add_zero,add_zero]

theorem generated_isPGroup {J : Type*} (weight : I→ℤ) (root : J→(Matrix I I K)ˣ)
    (hroot : ∀ a i j,weight i≤weight j→(root a : Matrix I I K) i j=(1 : Matrix I I K) i j)
    (p : ℕ) [Fact p.Prime] [CharP K p] : IsPGroup p (Subgroup.closure (Set.range root)) := by
  obtain ⟨e,he⟩ := CFSGFiniteWeightFlag.exists_flag weight
  have hL : Subgroup.closure (Set.range root)≤CFSGMatrixFlagSubgroups.unipotentUnits e := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    exact mem_unipotent_of_weight weight e he (root a) (hroot a)
  exact (CFSGMatrixFlagSubgroups.unipotentUnits_isPGroup e p).of_injective
    (Subgroup.inclusion hL) (Subgroup.inclusion_injective hL)

end SymmetricSubgroupAsymptotics.CFSGWeightedRootPGroup
