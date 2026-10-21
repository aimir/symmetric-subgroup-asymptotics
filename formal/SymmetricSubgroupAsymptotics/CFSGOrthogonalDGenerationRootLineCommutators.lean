import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays

/-! Full-parameter commutator closure in the original matrix-unit
subgroup. The four sparse factors are retained as actual subgroup
witnesses; no ambient classical group is substituted for that subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineCommutators
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootLineTransport
open CFSGOrthogonalDGenerationRootArrays
variable {K : Type} [Field K] {r : ℕ}

theorem commutator_line_transfer {I : Type*} [Fintype I] [DecidableEq I]
    (H : Subgroup (Matrix I I K)ˣ) (A B C : K → Matrix I I K)
    (hcomm : ∀ a b, A a * B b * A (-a) * B (-b) = C (a * b))
    (hA : HasRootLine H A) (hB : HasRootLine H B) : HasRootLine H C := by
  intro c
  obtain ⟨a, ha, hea⟩ := hA c
  obtain ⟨b, hb, heb⟩ := hB 1
  obtain ⟨a', ha', hea'⟩ := hA (-c)
  obtain ⟨b', hb', heb'⟩ := hB (-1)
  refine ⟨a * b * a' * b', H.mul_mem (H.mul_mem (H.mul_mem ha hb) ha') hb', ?_⟩
  change (a : Matrix I I K) * (b : Matrix I I K) * (a' : Matrix I I K) *
    (b' : Matrix I I K) = C c
  rw [hea, heb, hea', heb', hcomm, mul_one]

theorem chain_plus_lines (H : Subgroup (Mat K r)ˣ)
    (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hA : HasRootLine H (chainArray i j)) (hB : HasRootLine H (plusArray j k)) :
    HasRootLine H (plusArray i k) :=
  commutator_line_transfer H _ _ _ (chain_plus_commutator i j k hij hik hjk) hA hB

theorem plus_minus_lines (H : Subgroup (Mat K r)ˣ)
    (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hA : HasRootLine H (plusArray i k)) (hB : HasRootLine H (minusArray j k)) :
    HasRootLine H (chainArray i j) :=
  commutator_line_transfer H _ _ _ (plus_minus_commutator i j k hij hik hjk) hA hB

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineCommutators
