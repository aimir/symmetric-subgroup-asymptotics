import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays

/-! Parameter-sensitive paired-root symmetry. Reversing the paired
entries negates the parameter; full root lines retain this sign exactly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineSymmetries
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationSignedRootConjugation
open CFSGOrthogonalDGenerationRootArrays
variable (K : Type) [Field K]

theorem rootArray_paired {r : ℕ} (a b : Index r) (t : K) :
    rootArray K (paired b) (paired a) t = rootArray K a b (-t) := by
  cases a <;> cases b <;> ext x y <;>
    simp only [rootArray, paired, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply] <;>
      split_ifs <;> ring

theorem paired_line_transfer {r : ℕ} (H : Subgroup (Mat K r)ˣ) (a b : Index r)
    (hA : HasRootLine H (rootArray K a b)) :
    HasRootLine H (rootArray K (paired b) (paired a)) := by
  intro t
  obtain ⟨g, hg, he⟩ := hA (-t)
  exact ⟨g, hg, he.trans (rootArray_paired K a b t).symm⟩

theorem minusArray_eq_rootArray {r : ℕ} (i j : Fin r) (a : K) :
    minusArray i j a = rootArray K (Sum.inr j) (Sum.inl i) a := by
  simp only [minusArray, plusArray, rootArray, paired, Matrix.transpose_add,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_single]

theorem unit_mem_of_line {I : Type*} [Fintype I] [DecidableEq I]
    (H : Subgroup (Matrix I I K)ˣ) (A : K → Matrix I I K) (hA : HasRootLine H A)
    (u : (Matrix I I K)ˣ) (a : K) (hu : (u : Matrix I I K) = A a) : u ∈ H := by
  obtain ⟨g, hg, he⟩ := hA a
  exact (Units.ext (he.trans hu.symm)) ▸ hg

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineSymmetries
