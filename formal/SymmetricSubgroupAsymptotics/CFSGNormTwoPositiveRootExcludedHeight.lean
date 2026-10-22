import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExcludedHeight
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A positive norm-two coordinate root other than alpha_i has positive
excluded-i height. This follows from the actual integer norm, not from
an assumed table of roots or a type-specific enumeration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoPositiveRootExcludedHeight
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateHeight CFSGNormTwoCoordinateExcludedHeight
variable {r : ℕ}

theorem excludedHeight_eq_sum_erase (i : Fin r) (x : Fin r→ℤ) :
    excludedHeight i x=∑j∈Finset.univ.erase i,x j := by
  have hs := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
  change (∑j,x j)-x i=∑j∈Finset.univ.erase i,x j
  omega

theorem excludedHeight_nonneg (i : Fin r) (x : Fin r→ℤ) (hx : ∀j,0≤x j) :
    0≤excludedHeight i x := by
  rw [excludedHeight_eq_sum_erase]
  exact Finset.sum_nonneg (fun j _=>hx j)

theorem eq_simple_of_excluded_nonpos (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀j,A j j=2) (i : Fin r) (k : Roots A)
    (hpos : ∀j,0≤k.val j) (hexcl : excludedHeight i k.val≤0) :
    k=coordinateRoot A hd i := by
  have hzero : ∀j : Fin r,j≠i→k.val j=0 := by
    intro j hji
    have hj : j∈Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩
    have hle := Finset.single_le_sum (fun t (_ : t∈Finset.univ.erase i)=>hpos t) hj
    rw [←excludedHeight_eq_sum_erase] at hle
    have hjpos := hpos j
    omega
  let c : ℤ := k.val i
  have hvec : k.val=c • (Pi.single i 1 : Fin r→ℤ) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp [c,Pi.smul_apply]
    · rw [hzero j hji]
      simp [Pi.smul_apply,hji]
  have hn := k.property
  rw [hvec] at hn
  simp only [LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right,
    integerPairing,Matrix.toBilin'_single,hd] at hn
  have hcsq : c*c=1 := by nlinarith [hn]
  have hc : c=1 := by
    rcases mul_self_eq_one_iff.mp hcsq with h|h
    · exact h
    · have hcpos : 0≤c := hpos i
      omega
  apply Subtype.ext
  rw [hvec,hc,one_smul]
  rfl

theorem excludedHeight_positive (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀j,A j j=2) (i : Fin r) (k : Roots A)
    (hpos : ∀j,0≤k.val j) (hne : k≠coordinateRoot A hd i) :
    0<excludedHeight i k.val := by
  by_contra h
  exact hne (eq_simple_of_excluded_nonpos A hd i k hpos (le_of_not_gt h))

end SymmetricSubgroupAsymptotics.CFSGNormTwoPositiveRootExcludedHeight
