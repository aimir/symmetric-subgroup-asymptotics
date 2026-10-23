import SymmetricSubgroupAsymptotics.CFSGGTwoFullPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import SymmetricSubgroupAsymptotics.CFSGBlockMonomialBruhatUniqueness

/-! The actual eight-dimensional positive roots and torus preserve one
explicit complete flag. Bruhat monomial permutations are unique relative
to that flag; the argument does not identify any ordinary simple model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalBruhatFlag
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections CFSGGTwoPositivePGroup
open CFSGGTwoFullPositivePGroup CFSGGTwoNaturalRankTwoTorus

def coordinateOrder : Index ≃ Fin 8 where
  toFun := Sum.elim (fun i => ⟨i.val,by omega⟩) (fun i => ⟨7-i.val,by omega⟩)
  invFun r := if h : r.val<4 then Sum.inl ⟨r.val,h⟩ else Sum.inr ⟨7-r.val,by omega⟩
  left_inv i := by rcases i with i | i <;> fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem coordinateOrder_lt_iff (i j : Index) :
    coordinateOrder j<coordinateOrder i ↔ weight i<weight j := by
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> decide +kernel

variable (K : Type) [Field K]

def flagBorel : Subgroup ((Mat K)ˣ) := CFSGMatrixFlagSubgroups.borelUnits coordinateOrder

theorem positiveRoot_mem_flagBorel (j : Fin 6) (t : K) :
    positiveRoot K j t∈flagBorel K := by
  intro i k hik
  have hweight : weight i≤weight k := le_of_lt ((coordinateOrder_lt_iff i k).mp hik)
  rw [positiveRoot_identity_on_nonincreasing K j t i k hweight]
  have hne : i≠k := by rintro rfl; exact (lt_irrefl _ hik)
  simp only [Matrix.one_apply,if_neg hne]

theorem positiveGroup_le_flagBorel : positiveGroup K≤flagBorel K := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨j,t⟩,rfl⟩
  exact positiveRoot_mem_flagBorel K j t

theorem positiveRoot_mem_flagUnipotent (j : Fin 6) (t : K) :
    positiveRoot K j t∈CFSGMatrixFlagSubgroups.unipotentUnits coordinateOrder := by
  refine ⟨positiveRoot_mem_flagBorel K j t,?_⟩
  intro i
  exact (positiveRoot_identity_on_nonincreasing K j t i i le_rfl).trans
    (Matrix.one_apply_eq i)

theorem positiveGroup_le_flagUnipotent :
    positiveGroup K≤CFSGMatrixFlagSubgroups.unipotentUnits coordinateOrder := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨j,t⟩,rfl⟩
  exact positiveRoot_mem_flagUnipotent K j t

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2=c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3=d := rfl

def diagonalWeight (t : Kˣ × Kˣ) : Index → K := pairAction K t (fun _ => 1)

theorem pairAction_eq_mul (t : Kˣ × Kˣ) (v : Index → K) (i : Index) :
    pairAction K t v i=diagonalWeight K t i*v i := by
  rcases i with i | i <;> fin_cases i <;>
    simp [pairAction,diagonalWeight,pos,neg,vec4_two,vec4_three,mul_assoc]

theorem torusPair_diagonal (t : Kˣ × Kˣ) :
    ((torusPair K t).val : Mat K)=Matrix.diagonal (diagonalWeight K t) := by
  apply Matrix.ext
  intro i j
  have he : ((torusPair K t).val : Mat K) i j=
      pairAction K t (Pi.single j 1) i := by
    calc
      _=(((torusPair K t).val : Mat K)*ᵥ Pi.single j 1) i :=
        (congrFun (Matrix.mulVec_single_one ((torusPair K t).val : Mat K) j) i).symm
      _=_ := congrFun (torusPair_apply K t (Pi.single j 1)) i
  rw [he,pairAction_eq_mul]
  by_cases h : i=j
  · subst j
    simp
  · simp [Pi.single_apply,Function.update,h,Ne.symm h,Matrix.diagonal_apply]

theorem torusPair_mem_flagBorel (t : Kˣ × Kˣ) : (torusPair K t).val∈flagBorel K := by
  intro i j hij
  rw [torusPair_diagonal]
  have hne : i≠j := by rintro rfl; exact (lt_irrefl _ hij)
  simp [Matrix.diagonal_apply,hne]

def columnPermutation (sigma : Equiv.Perm Index) : Equiv.Perm (Fin 8) :=
  coordinateOrder.permCongr sigma.symm

theorem monomial_permutation_unique
    (B1 B2 W1 W2 : (Mat K)ˣ) (hB1 : B1∈flagBorel K) (hB2 : B2∈flagBorel K)
    (sigma1 sigma2 : Equiv.Perm Index) (d1 d2 : Index → K)
    (hW1 : (W1 : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma1 d1)
    (hW2 : (W2 : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma2 d2)
    (he : B1*W1*B2=W2) : sigma1=sigma2 := by
  have support (W : (Mat K)ˣ) (sigma : Equiv.Perm Index) (d : Index → K)
      (hW : (W : Mat K)=CFSGTypeAMonomialMatrices.monomial sigma d) :
      ∀ i j, coordinateOrder i≠columnPermutation sigma (coordinateOrder j) →
        (W : Mat K) i j=0 := by
    intro i j hij
    rw [hW,CFSGTypeAMonomialMatrices.monomial_apply]
    have hne : sigma i≠j := by
      intro hs
      apply hij
      rw [←hs]
      simp [columnPermutation]
    exact if_neg hne
  have hp := CFSGBlockMonomialBruhatUniqueness.block_bruhat_permutation_unique
    coordinateOrder coordinateOrder.surjective B1 B2 W1 W2 hB1 hB2
    (columnPermutation sigma1) (columnPermutation sigma2)
    (support W1 sigma1 d1 hW1) (support W2 sigma2 d2 hW2) he
  have hs : sigma1⁻¹=sigma2⁻¹ := coordinateOrder.permCongrHom.injective hp
  exact inv_injective hs

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalBruhatFlag
