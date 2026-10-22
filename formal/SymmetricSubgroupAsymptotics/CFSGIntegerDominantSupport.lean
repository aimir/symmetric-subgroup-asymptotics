import SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing

/-! Elementary support propagation for a nonnegative dominant vector
in an integral matrix with nonpositive off-diagonal entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegerDominantSupport
open CFSGIntegerMatrixPairing
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem pairing_coordinate_sum_left (B : LinearMap.BilinForm ℤ (I→ℤ)) (x y : I→ℤ) :
    B x y=∑i,x i*B (Pi.single i (1:ℤ) : I→ℤ) y := by
  have hx : (∑i,x i • (Pi.single i (1:ℤ) : I→ℤ))=x := by
    calc
      _=∑i,(Pi.single i (x i) : I→ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        funext j
        by_cases hij : i=j <;> simp [Pi.smul_apply,Pi.single_apply,smul_eq_mul,hij]
      _=x := LinearMap.sum_single_apply (fun _ : I=>ℤ) x
  calc
    _=B (∑i,x i • (Pi.single i (1:ℤ) : I→ℤ)) y := congrArg (fun z=>B z y) hx.symm
    _=_ := by simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]

theorem matrix_pairing_single_right (A : Matrix I I ℤ) (x : I→ℤ) (j : I) :
    integerPairing A x (Pi.single j (1:ℤ) : I→ℤ)=∑i,x i*A i j := by
  rw [pairing_coordinate_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integerPairing,Matrix.toBilin'_single]

theorem dominant_zero_propagates (A : Matrix I I ℤ)
    (ho : ∀i j,i≠j→A i j≤0) (x : I→ℤ) (hx : ∀i,0≤x i)
    (hdom : ∀j,0 ≤ integerPairing A x (Pi.single j (1:ℤ) : I→ℤ))
    (j i : I) (hj : x j=0) (hij : A i j≠0) : x i=0 := by
  have hnp : ∀a∈Finset.univ,x a*A a j≤0 := by
    intro a ha
    by_cases haj : a=j
    · subst a
      rw [hj,zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hx a) (ho a j haj)
  have hsum : (∑a,x a*A a j)=0 := by
    apply le_antisymm (Finset.sum_nonpos hnp)
    rw [←matrix_pairing_single_right]
    exact hdom j
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsum i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hz).resolve_right hij

end SymmetricSubgroupAsymptotics.CFSGIntegerDominantSupport
