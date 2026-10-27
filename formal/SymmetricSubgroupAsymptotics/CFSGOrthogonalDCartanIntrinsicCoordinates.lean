import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanParitySpan

/-! A uniform coordinate inverse for the intrinsic D Cartan lattice.
Rational half-sums prove independence, while the actual even-sum span
supplies surjectivity over Z; no ambient integral splitting is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDCartanParityLattice
open CFSGOrthogonalDCartanParitySpan
variable (r : ℕ)

def prefixSum (b : ℕ) : (Fin r→ℤ)→ₗ[ℤ]ℤ where
  toFun a:=∑ j ∈ Finset.univ.filter (fun j : Fin r=>j.val ≤ b),a j
  map_add' a b:=by simp [Finset.sum_add_distrib]
  map_smul' z a:=by simp [←Finset.mul_sum]

def total : (Fin r→ℤ)→ₗ[ℤ]ℤ where
  toFun a:=∑ j,a j
  map_add' a b:=by simp [Finset.sum_add_distrib]
  map_smul' z a:=by simp [←Finset.mul_sum]

def castLinear : ℤ→ₗ[ℤ]ℚ := (Int.castAddHom ℚ).toIntLinearMap

theorem prefix_unit (b : ℕ) (i : Fin r) :
    prefixSum r b (unit r i)=if i.val ≤ b then 1 else 0 := by
  classical
  simp [prefixSum,unit,Pi.single_apply]

theorem prefix_column (hr : 4 ≤ r) (b : Fin r) (hb : b.val+2 < r) (i : Fin r) :
    prefixSum r b.val (column r i)=if i=b then 1 else 0 := by
  rw [column_eq r hr]
  by_cases hi : i.val+1 < r
  · rw [dif_pos hi,map_sub,prefix_unit,prefix_unit]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [dif_neg hi,map_add,prefix_unit,prefix_unit]
    simp only [previous_val,Fin.ext_iff]
    have hil:=i.isLt
    split_ifs <;> omega

theorem last_column (hr : 4 ≤ r) (i : Fin r) :
    column r i ⟨r-1,by omega⟩=
      if i.val+1 < r then (if i.val+2=r then -1 else 0) else 1 := by
  rw [column_eq r hr]
  by_cases hi : i.val+1 < r
  · rw [dif_pos hi]
    simp only [Pi.sub_apply,unit,Pi.single_apply,Fin.ext_iff]
    have hil:=i.isLt
    split_ifs <;> omega
  · rw [dif_neg hi]
    simp only [Pi.add_apply,unit,Pi.single_apply,Fin.ext_iff,previous_val]
    have hil:=i.isLt
    split_ifs <;> omega

def rationalCoordinates (hr : 4 ≤ r) : (Fin r→ℤ)→ₗ[ℤ](Fin r→ℚ) :=
  LinearMap.pi (fun i=>
    if i.val+2 < r then castLinear.comp (prefixSum r i.val)
    else if i.val+1 < r then
      (1/2:ℚ) • (castLinear.comp (total r))-
        castLinear.comp (LinearMap.proj (⟨r-1,by omega⟩ : Fin r))
    else (1/2:ℚ) • (castLinear.comp (total r)))

theorem rationalCoordinates_column (hr : 4 ≤ r) (j : Fin r) :
    rationalCoordinates r hr (column r j)=Pi.single j 1 := by
  funext i
  by_cases hi : i.val+2 < r
  · simp only [rationalCoordinates,LinearMap.pi_apply,if_pos hi,LinearMap.comp_apply]
    change (prefixSum r i.val (column r j):ℚ)=(Pi.single j (1:ℚ) : Fin r→ℚ) i
    rw [prefix_column r hr i hi]
    simp [Pi.single_apply,eq_comm]
  · by_cases hi' : i.val+1 < r
    · simp only [rationalCoordinates,LinearMap.pi_apply,if_neg hi,if_pos hi',
        LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply]
      change (1/2:ℚ)*((∑ k,column r j k:ℤ):ℚ)-(column r j ⟨r-1,by omega⟩:ℚ)=
        (Pi.single j (1:ℚ) : Fin r→ℚ) i
      rw [column_sum r hr,last_column r hr]
      simp only [Pi.single_apply,Fin.ext_iff]
      have hil:=i.isLt
      have hjl:=j.isLt
      split_ifs <;> norm_num at * <;> omega
    · simp only [rationalCoordinates,LinearMap.pi_apply,if_neg hi,if_neg hi',
        LinearMap.smul_apply,LinearMap.comp_apply]
      change (1/2:ℚ)*((∑ k,column r j k:ℤ):ℚ)=(Pi.single j (1:ℚ) : Fin r→ℚ) i
      rw [column_sum r hr]
      simp only [Pi.single_apply,Fin.ext_iff]
      have hil:=i.isLt
      have hjl:=j.isLt
      split_ifs <;> norm_num at * <;> omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicCoordinates
