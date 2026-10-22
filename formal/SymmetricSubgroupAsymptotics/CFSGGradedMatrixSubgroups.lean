import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport

/-! Actual matrix-unit subgroups preserving grading blocks, and acting
as the identity on the associated graded space. Their intersection is
trivial; this is a support statement, including in bad characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
open CFSGGradedMatrixSupport
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

private theorem inverse_blockTriangular (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : (u : Matrix I I K).BlockTriangular weight) :
    (↑(u⁻¹) : Matrix I I K).BlockTriangular weight := by
  letI : Invertible (u : Matrix I I K) := u.invertible
  have hi : (u : Matrix I I K)⁻¹=(↑(u⁻¹) : Matrix I I K) :=
    Matrix.inv_eq_left_inv (Units.inv_mul u)
  rw [←hi]
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

private theorem inverse_supported (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : Supported weight id (u : Matrix I I K)) :
    Supported weight id (↑(u⁻¹) : Matrix I I K) := by
  have hpos : (u : Matrix I I K).BlockTriangular weight := by
    intro i j hij
    exact hu i j (by dsimp only [id];omega)
  have hneg : (u : Matrix I I K).BlockTriangular (fun i=> -weight i) := by
    intro i j hij
    change -weight j < -weight i at hij
    exact hu i j (by dsimp only [id];omega)
  have hpi := inverse_blockTriangular weight u hpos
  have hni := inverse_blockTriangular (fun i=> -weight i) u hneg
  intro i j hij
  change weight i≠weight j at hij
  rcases lt_or_gt_of_ne hij with h|h
  · have hh : -weight j < -weight i := by omega
    exact hni hh
  · exact hpi h

def preservingUnits (weight : I→ℤ) : Subgroup (Matrix I I K)ˣ where
  carrier := {u | Supported weight id (u : Matrix I I K)}
  one_mem' := supported_one weight
  mul_mem' := by
    intro u v hu hv
    exact supported_congr (supported_mul hu hv) (fun _=>rfl)
  inv_mem' := by
    intro u hu
    exact inverse_supported weight u hu

private theorem strict_mul (weight : I→ℤ) (M N : Matrix I I K)
    (hM : ∀ i j,weight i≤weight j→M i j=(1 : Matrix I I K) i j)
    (hN : ∀ i j,weight i≤weight j→N i j=(1 : Matrix I I K) i j) :
    ∀ i j,weight i≤weight j→(M*N) i j=(1 : Matrix I I K) i j := by
  intro i j hij
  rw [Matrix.mul_apply]
  calc
    (∑ k,M i k*N k j)=M i i*N i j := by
      apply Finset.sum_eq_single i
      · intro k _ hki
        by_cases hik : weight i≤weight k
        · rw [hM i k hik,Matrix.one_apply,if_neg (Ne.symm hki),zero_mul]
        · have hkj : weight k≤weight j := by omega
          have hne : k≠j := by intro h;subst k;omega
          rw [hN k j hkj,Matrix.one_apply,if_neg hne,mul_zero]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
    _=(1 : Matrix I I K) i j := by
      rw [hM i i le_rfl,Matrix.one_apply_eq,one_mul,hN i j hij]

private theorem strict_inverse (weight : I→ℤ) (u : (Matrix I I K)ˣ)
    (hu : ∀ i j,weight i≤weight j→(u : Matrix I I K) i j=(1 : Matrix I I K) i j) :
    ∀ i j,weight i≤weight j→(↑(u⁻¹) : Matrix I I K) i j=(1 : Matrix I I K) i j := by
  have htri : (u : Matrix I I K).BlockTriangular (fun i=> -weight i) := by
    intro i j hij
    change -weight j < -weight i at hij
    have hne : i≠j := by intro h;subst j;omega
    rw [hu i j (by omega),Matrix.one_apply,if_neg hne]
  have hinv := inverse_blockTriangular (fun i=> -weight i) u htri
  intro i j hij
  have he : ((u : Matrix I I K)*(↑(u⁻¹) : Matrix I I K)) i j=
      (↑(u⁻¹) : Matrix I I K) i j := by
    rw [Matrix.mul_apply]
    calc
      (∑ k,(u : Matrix I I K) i k*(↑(u⁻¹) : Matrix I I K) k j)=
          (u : Matrix I I K) i i*(↑(u⁻¹) : Matrix I I K) i j := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          by_cases hik : weight i≤weight k
          · rw [hu i k hik,Matrix.one_apply,if_neg (Ne.symm hki),zero_mul]
          · have hkj : -weight j < -weight k := by omega
            rw [hinv hkj,mul_zero]
        · intro h
          exact False.elim (h (Finset.mem_univ i))
      _=(↑(u⁻¹) : Matrix I I K) i j := by
        rw [hu i i le_rfl,Matrix.one_apply_eq,one_mul]
  have hh := congrArg (fun M : Matrix I I K=>M i j) (Units.mul_inv u)
  change ((u : Matrix I I K)*(↑(u⁻¹) : Matrix I I K)) i j=(1 : Matrix I I K) i j at hh
  rw [he] at hh
  exact hh

def strictUnits (weight : I→ℤ) : Subgroup (Matrix I I K)ˣ where
  carrier := {u | ∀ i j,weight i≤weight j→(u : Matrix I I K) i j=(1 : Matrix I I K) i j}
  one_mem' := fun _ _ _=>rfl
  mul_mem' := fun hu hv=>strict_mul weight _ _ hu hv
  inv_mem' := by
    intro u hu
    exact strict_inverse weight u hu

theorem strict_inf_preserving (weight : I→ℤ) :
    strictUnits (K:=K) weight⊓preservingUnits weight=⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [Subgroup.mem_bot]
  apply Units.ext
  have hp : Supported weight id (u : Matrix I I K) := hu.2
  have hs : ∀ i j,weight i≤weight j→
      (u : Matrix I I K) i j=(1 : Matrix I I K) i j := hu.1
  exact eq_one_of_preserves_of_nonincreasing hp hs

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
