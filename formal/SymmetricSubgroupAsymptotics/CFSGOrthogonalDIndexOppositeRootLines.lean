import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationChainCommutators

/-! Literal positive U root lines and a transposed sparse commutator.
These will prove generation by U and one actual Coxeter conjugate of U;
no longest-element, building, or full-orthogonal-group theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeRootLines
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveChains CFSGOrthogonalDIndexPositiveRoots
open CFSGOrthogonalDIndexPositiveCentralizer CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationRootLineCommutators
variable (K : Type) [Field K]

def ambientUnipotent (r : ℕ) : Subgroup (Mat K r)ˣ :=
  (unipotent K r).map (elementaryRootGroup K r).subtype

theorem positive_chain_line (r : ℕ) (i j : Fin r) (hij : i < j) :
    HasRootLine (ambientUnipotent K r) (chainArray i j) := by
  intro a
  refine ⟨(chainInU K r i j hij a).val.val, ?_, ?_⟩
  · exact ⟨(chainInU K r i j hij a).val, (chainInU K r i j hij a).property, rfl⟩
  · exact chainElement_val K r i j (ne_of_lt hij) a

theorem positive_plus_line (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) :
    HasRootLine (ambientUnipotent K (s + 4)) (plusArray i j) := by
  intro a
  refine ⟨(pairInU K s i j hij a).val.val, ?_, ?_⟩
  · exact ⟨(pairInU K s i j hij a).val, (pairInU K s i j hij a).property, rfl⟩
  · rw [pairInU_val]
    simp only [pairedUpper, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, plusArray]
    abel

theorem chainArray_transpose {r : ℕ} (i j : Fin r) (a : K) :
    (chainArray i j a).transpose = chainArray j i a := by
  simp only [chainArray, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_single]

theorem plusArray_transpose {r : ℕ} (i j : Fin r) (a : K) :
    (plusArray i j a).transpose = minusArray i j a := rfl

theorem minus_chain_commutator {r : ℕ} (i j k : Fin r)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : K) :
    minusArray j k a * chainArray j i b * minusArray j k (-a) * chainArray j i (-b) =
      minusArray i k (a * b) := by
  have h := congrArg Matrix.transpose (chain_plus_commutator i j k hij hik hjk (-b) (-a))
  simp only [Matrix.transpose_mul, chainArray_transpose, plusArray_transpose] at h
  simpa only [neg_neg, neg_mul_neg, mul_comm, mul_assoc] using h

theorem minus_chain_lines {r : ℕ} (H : Subgroup (Mat K r)ˣ)
    (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hM : HasRootLine H (minusArray j k)) (hC : HasRootLine H (chainArray j i)) :
    HasRootLine H (minusArray i k) :=
  commutator_line_transfer H _ _ _ (minus_chain_commutator K i j k hij hik hjk) hM hC

theorem conjugate_line_in {I : Type} [Fintype I] [DecidableEq I]
    (H S : Subgroup (Matrix I I K)ˣ) (Y : (Matrix I I K)ˣ)
    (hSY : S.map (MulAut.conj Y).toMonoidHom ≤ H)
    (A B : K → Matrix I I K) (c : K) (hc : c ≠ 0)
    (hconj : ∀ a, (Y : Matrix I I K) * A a * (↑Y⁻¹ : Matrix I I K) = B (c * a))
    (hA : HasRootLine S A) : HasRootLine H B := by
  intro b
  obtain ⟨g, hg, he⟩ := hA (b / c)
  refine ⟨Y * g * Y⁻¹, hSY ⟨g, hg, rfl⟩, ?_⟩
  change (Y : Matrix I I K) * (g : Matrix I I K) * (↑Y⁻¹ : Matrix I I K) = B b
  rw [he, hconj, mul_div_cancel₀ _ hc]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeRootLines
