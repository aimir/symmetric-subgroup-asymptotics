import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalBrackets
import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation

/-! Actual type-A Serre interval vectors, in every rank. Out-of-range
indices are zero only for convenient recursion; every valid node is the
literal original source generator. Far and adjacent relations come from
the defining original Serre quotient, not matrix injectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreCrossNodeCommutation
open CFSGTwistedAIntervalBrackets

abbrev Source (r : ℕ) := RationalLie (CartanMatrix.A r)

def simple (r : ℕ) (neg : Bool) (i : ℕ) : Source r :=
  if hi : i < r then rootVector (CartanMatrix.A r) neg ⟨i, hi⟩ else 0

def interval (r : ℕ) (neg : Bool) (start n : ℕ) : Source r :=
  chainBracket (simple r neg) start n

theorem simple_at (r : ℕ) (neg : Bool) (i : Fin r) :
    simple r neg i.val = rootVector (CartanMatrix.A r) neg i := by
  simp only [simple, dif_pos i.isLt]

theorem cartan_far {r : ℕ} (i j : Fin r)
    (hgap : i.val + 1 < j.val ∨ j.val + 1 < i.val) : CartanMatrix.A r i j = 0 := by
  have hne : i ≠ j := by intro he; have hh := congrArg (fun x : Fin r => x.val) he; omega
  have ha : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne, if_neg ha]

theorem cartan_adjacent {r : ℕ} (i j : Fin r)
    (ha : i.val + 1 = j.val ∨ j.val + 1 = i.val) : CartanMatrix.A r i j = -1 := by
  have hne : i ≠ j := by intro he; have hh := congrArg (fun x : Fin r => x.val) he; omega
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne, if_pos ha]

theorem simple_lie_far (r : ℕ) (neg : Bool) (i j : ℕ)
    (hgap : i + 1 < j ∨ j + 1 < i) : ⁅simple r neg i, simple r neg j⁆ = 0 := by
  by_cases hi : i < r
  · by_cases hj : j < r
    · simp only [simple, dif_pos hi, dif_pos hj]
      exact rootVector_lie_zero_of_cartan_zero (CartanMatrix.A r) neg ⟨i, hi⟩ ⟨j, hj⟩
        (cartan_far _ _ hgap)
    · simp only [simple, dif_pos hi, dif_neg hj, lie_zero]
  · simp only [simple, dif_neg hi, zero_lie]

theorem simple_serre_adjacent (r : ℕ) (neg : Bool) (i j : ℕ)
    (ha : i + 1 = j ∨ j + 1 = i) :
    ⁅simple r neg i, ⁅simple r neg i, simple r neg j⁆⁆ = 0 := by
  by_cases hi : i < r
  · by_cases hj : j < r
    · simp only [simple, dif_pos hi, dif_pos hj]
      have hA := cartan_adjacent (⟨i, hi⟩ : Fin r) ⟨j, hj⟩ ha
      cases neg
      · have h := generator_adE (CartanMatrix.A r) (⟨i, hi⟩ : Fin r) ⟨j, hj⟩
        rw [hA] at h
        change ⁅rootVector (CartanMatrix.A r) false ⟨i, hi⟩,
          ⁅rootVector (CartanMatrix.A r) false ⟨i, hi⟩,
            rootVector (CartanMatrix.A r) false ⟨j, hj⟩⁆⁆ = 0 at h
        exact h
      · have h := generator_adF (CartanMatrix.A r) (⟨i, hi⟩ : Fin r) ⟨j, hj⟩
        rw [hA] at h
        change ⁅rootVector (CartanMatrix.A r) true ⟨i, hi⟩,
          ⁅rootVector (CartanMatrix.A r) true ⟨i, hi⟩,
            rootVector (CartanMatrix.A r) true ⟨j, hj⟩⁆⁆ = 0 at h
        exact h
    · simp only [simple, dif_pos hi, dif_neg hj, lie_zero]
  · simp only [simple, dif_neg hi, zero_lie]

theorem simple_interval_far (r : ℕ) (neg : Bool) (k start n : ℕ)
    (hgap : k + 1 < start ∨ start + n < k) :
    ⁅simple r neg k, interval r neg start n⁆ = 0 :=
  lie_chainBracket_far (simple r neg) (simple_lie_far r neg) k start n hgap

theorem simple_interval_right (r : ℕ) (neg : Bool) (start n : ℕ) (hn : 0 < n) :
    ⁅simple r neg (start + n), interval r neg start n⁆ = -interval r neg start (n + 1) :=
  lie_chainBracket_right (simple r neg) (simple_lie_far r neg) start n hn

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
