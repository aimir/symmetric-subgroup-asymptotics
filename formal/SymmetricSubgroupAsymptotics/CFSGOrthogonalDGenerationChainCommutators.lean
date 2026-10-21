import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineCommutators

/-! The natural A-chain commutator inside the original D matrix
coordinates, with its complete field parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationChainCommutators
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationRootLineCommutators
variable {K : Type} [Field K] {r : ℕ}

theorem chain_chain_commutator (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : K) :
    chainArray i j a * chainArray j k b * chainArray i j (-a) * chainArray j k (-b) =
      chainArray i k (a * b) := by
  simp [chainArray, mul_add, add_mul, mul_sub, sub_mul,
    hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk] <;>
    (ext x y; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.single_apply]; split_ifs <;> ring)

theorem chain_chain_lines (H : Subgroup (Mat K r)ˣ)
    (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hA : HasRootLine H (chainArray i j)) (hB : HasRootLine H (chainArray j k)) :
    HasRootLine H (chainArray i k) :=
  commutator_line_transfer H _ _ _ (chain_chain_commutator i j k hij hik hjk) hA hB

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationChainCommutators
