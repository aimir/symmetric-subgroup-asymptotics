import SymmetricSubgroupAsymptotics.BinaryFourFullBlockPermutation

/-! A common radical argument for the full four-block module. A subspace
stable under the actual Klein and ternary operators is either contained
in augmentation or is the whole module. Only its two block-sum entries
are split into finite cases; subspaces are not enumerated. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation

theorem fullC_power_augmentation (n : ℕ) (x : FullCoordinates) :
    augmentation ((fullC ^ n) x) = (localCycle ^ n) (augmentation x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change augmentation (fullC ((fullC ^ n) x)) =
        localCycle ((localCycle ^ n) (augmentation x))
      rw [fullC_augmentation, ih]

theorem fullSpace_eq_top_of_nonzero_augmentation
    (W : Submodule Scalar FullCoordinates)
    (hU : ∀ x ∈ W, fullU x ∈ W)
    (hV : ∀ x ∈ W, fullV x ∈ W)
    (hC : ∀ x ∈ W, fullC x ∈ W)
    (x : FullCoordinates) (hx : x ∈ W) (ha : augmentation x ≠ 0) : W = ⊤ := by
  have rotate : ∀ a : Local, a ≠ 0 →
      ∃ n : Fin 3, (localCycle ^ n.val) a = ![1, 0] := by decide +kernel
  obtain ⟨n, hn⟩ := rotate (augmentation x) ha
  have hpow (m : ℕ) : (fullC ^ m) x ∈ W := by
    induction m with
    | zero => exact hx
    | succ m ih =>
        rw [pow_succ']
        exact hC _ ih
  let y := (fullC ^ n.val) x
  have hy : y ∈ W := hpow n.val
  have hyaug : augmentation y = ![1, 0] := (fullC_power_augmentation n.val x).trans hn
  have hy6 : y 6 = 1 := congrFun hyaug 0
  have hy7 : y 7 = 0 := congrFun hyaug 1
  have h0 : fullBasis 0 ∈ W := by
    have he : fullU (fullV y) + fullV y + fullU y + y = fullBasis 0 := by
      ext i
      simp only [Pi.add_apply]
      fin_cases i <;> simp [fullU, fullV, fullBasis, hy6, hy7] <;>
        ring_nf <;> simp only [show (2 : Scalar) = 0 from by decide +kernel,
          show (3 : Scalar) = 1 from by decide +kernel,
          show (4 : Scalar) = 0 from by decide +kernel,
          mul_zero, add_zero]
    rw [← he]
    exact W.add_mem (W.add_mem (W.add_mem (hU _ (hV _ hy)) (hV _ hy)) (hU _ hy)) hy
  have h1 : fullBasis 1 ∈ W := by
    have he : fullC (fullBasis 0) + fullBasis 0 = fullBasis 1 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact W.add_mem (hC _ h0) h0
  have h3 : fullBasis 3 ∈ W := by
    have he : fullU y + y + (y 4 + y 5) • fullBasis 0 +
        (y 2 + y 4 + y 5) • fullBasis 1 = fullBasis 3 := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      fin_cases i <;> simp [fullU, fullBasis, hy6, hy7] <;>
        ring_nf <;> simp only [show (2 : Scalar) = 0 from by decide +kernel,
          mul_zero, add_zero]
    rw [← he]
    exact W.add_mem (W.add_mem (W.add_mem (hU _ hy) hy)
      (W.smul_mem _ h0)) (W.smul_mem _ h1)
  have h4 : fullBasis 4 ∈ W := by
    have he : fullC (fullBasis 3) = fullBasis 4 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact hC _ h3
  have h2 : fullBasis 2 ∈ W := by
    have he : fullC (fullBasis 4) = fullBasis 2 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact hC _ h4
  have h5 : fullBasis 5 ∈ W := by
    have he : fullV y + y + (y 3 + y 4 + 1) • fullBasis 0 +
        (y 4 + 1) • fullBasis 1 + fullBasis 2 = fullBasis 5 := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      fin_cases i <;> simp [fullV, fullBasis, hy6, hy7] <;>
        ring_nf <;> simp only [show (2 : Scalar) = 0 from by decide +kernel,
          mul_zero, add_zero]
    rw [← he]
    exact W.add_mem (W.add_mem (W.add_mem (W.add_mem (hV _ hy) hy)
      (W.smul_mem _ h0)) (W.smul_mem _ h1)) h2
  have h6 : fullBasis 6 ∈ W := by
    have he : y + y 0 • fullBasis 0 + y 1 • fullBasis 1 + y 2 • fullBasis 2 +
        y 3 • fullBasis 3 + y 4 • fullBasis 4 + y 5 • fullBasis 5 = fullBasis 6 := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      fin_cases i <;> simp [fullBasis, hy6, hy7]
    rw [← he]
    exact W.add_mem (W.add_mem (W.add_mem (W.add_mem (W.add_mem (W.add_mem hy
      (W.smul_mem _ h0)) (W.smul_mem _ h1)) (W.smul_mem _ h2))
      (W.smul_mem _ h3)) (W.smul_mem _ h4)) (W.smul_mem _ h5)
  have h7 : fullBasis 7 ∈ W := by
    have he : fullC (fullBasis 6) + fullBasis 6 = fullBasis 7 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact W.add_mem (hC _ h6) h6
  have hb : ∀ i : Fin 8, fullBasis i ∈ W := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  apply top_unique
  rw [← (Pi.basisFun Scalar (Fin 8)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  simpa only [Pi.basisFun_apply] using hb i

theorem fullSpace_eq_top_or_augmentation
    (W : Submodule Scalar FullCoordinates)
    (hU : ∀ x ∈ W, fullU x ∈ W)
    (hV : ∀ x ∈ W, fullV x ∈ W)
    (hC : ∀ x ∈ W, fullC x ∈ W) :
    W = ⊤ ∨ ∀ x ∈ W, augmentation x = 0 := by
  by_cases h : ∀ x ∈ W, augmentation x = 0
  · exact Or.inr h
  · push Not at h
    obtain ⟨x, hx, ha⟩ := h
    exact Or.inl (fullSpace_eq_top_of_nonzero_augmentation W hU hV hC x hx ha)

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
