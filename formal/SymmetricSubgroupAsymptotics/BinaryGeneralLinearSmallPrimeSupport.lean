import SymmetricSubgroupAsymptotics.BinaryGeneralLinearMatchingPrimeMultiplicity
import SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics

/-! The actual GL orders in dimensions at most six have one shared
small prime support. The finite reductions concern seven integer order
divisibilities and one integer factorization, never linear-group elements,
subgroups, action tables or group-classification rows. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallPrimeSupport
open BinaryAffineJointSelectedWindowNumerics BinaryGeneralLinearMatchingPrimeMultiplicity

theorem GL_card_dvd_six (d : ℕ) (hd : d ≤ 6) :
    Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) := by
  rw [matrix_GL_card_eq_order,matrix_GL_card_eq_order]
  have hh : ∀ k : Fin 7, binaryGLOrder (k : ℕ) ∣ binaryGLOrder 6 := by decide +kernel
  exact hh ⟨d,by omega⟩

theorem GL_six_primeFactors :
    (Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))).primeFactors =
      ({2,3,5,7,31} : Finset ℕ) := by
  rw [matrix_GL_card_eq_order]
  decide +kernel

theorem GL_primeFactors_subset (d : ℕ) (hd : d ≤ 6) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).primeFactors ⊆
      ({2,3,5,7,31} : Finset ℕ) := by
  have hh := Nat.primeFactors_mono (GL_card_dvd_six d hd)
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))).ne'
  simpa only [GL_six_primeFactors] using hh

theorem matchingMultiplicity_eq_zero (d q : ℕ) (hd : d ≤ 6)
    (hq : q ∉ ({2,3,5,7,31} : Finset ℕ)) : matchingMultiplicity d q = 0 := by
  have hnot : q ∉ (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).primeFactors :=
    fun hmem => hq (GL_primeFactors_subset d hd hmem)
  have hz : (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).factorization q = 0 := by
    by_contra hne
    exact hnot (Finsupp.mem_support_iff.mpr hne)
  have hq2 : q ≠ 2 := by
    intro heq
    subst q
    exact hq (by decide)
  simp only [matchingMultiplicity,hz,if_neg hq2,add_zero]

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallPrimeSupport
