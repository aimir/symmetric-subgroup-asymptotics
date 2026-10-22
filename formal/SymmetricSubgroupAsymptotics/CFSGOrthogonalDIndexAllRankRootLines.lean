import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairPermutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSignedCoordinateRoots
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTranspose

/-! Every chain and upper/lower skew root line belongs to the literal
natural D group already for rank>=2. A signed SL permutation transports
the actual terminal root. This supports the genuine D3 tail without
identifying it with a named low-rank model or using a census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankRootLines
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationSignedPermutation
open CFSGOrthogonalDIndexSignedCoordinateRoots CFSGOrthogonalDIndexPairPermutation
open CFSGOrthogonalDIndexPositiveChains CFSGOrthogonalDIndexTranspose
variable (K : Type) [Field K]

theorem terminal_root_array (r : ℕ) (hr : 2 ≤ r) (a : K) :
    ((rootTransvection K r false (⟨r - 1, by omega⟩ : Fin r) a) : Mat K r) =
      plusArray (⟨r - 2, by omega⟩ : Fin r) (⟨r - 1, by omega⟩ : Fin r) a := by
  let p : Fin r := ⟨r - 2, by omega⟩
  let l : Fin r := ⟨r - 1, by omega⟩
  have hl : ¬l.val + 1 < r := by dsimp [l]; omega
  have hp : previous r l = p := by
    apply Fin.ext
    dsimp [previous, l, p]
    omega
  change 1 + a • positive K r l = plusArray p l a
  rw [positive, dif_neg hl, hp]
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, plusArray]
  abel

theorem plus_line_all_ranks (r : ℕ) (hr : 2 ≤ r) (i j : Fin r) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K r) (plusArray i j) := by
  let p : Fin r := ⟨r - 2, by omega⟩
  let l : Fin r := ⟨r - 1, by omega⟩
  have hpl : p ≠ l := by
    intro h
    have he := congrArg Fin.val h
    change r - 2 = r - 1 at he
    omega
  let σ := pairPermutation i j p l
  have hσi : σ.symm p = i := by
    have h := pairPermutation_first i j p l hij hpl
    change σ i = p at h
    rw [← h, Equiv.symm_apply_apply]
  have hσj : σ.symm l = j := by
    have h := pairPermutation_second i j p l
    change σ j = l at h
    rw [← h, Equiv.symm_apply_apply]
  have hterminal : HasRootLine (elementaryRootGroup K r) (plusArray p l) := by
    intro a
    exact ⟨rootTransvection K r false l a, rootTransvection_mem K r false l a,
      terminal_root_array K r hr a⟩
  let W := signedPermutationElement K r l σ
  have ht : HasRootLine (elementaryRootGroup K r) (plusArray (σ.symm p) (σ.symm l)) := by
    apply conjugate_transfer (elementaryRootGroup K r) W.val W.property _ _
      (weight K l σ (σ.symm p) / weight K l σ (σ.symm l))
      (div_ne_zero (weight_ne_zero K l σ (σ.symm p)) (weight_ne_zero K l σ (σ.symm l)))
      _ hterminal
    intro a
    rw [signedPermutation_plus_conjugation, div_mul_eq_mul_div]
  rw [hσi, hσj] at ht
  exact ht

theorem minus_line_all_ranks (r : ℕ) (hr : 2 ≤ r) (i j : Fin r) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K r) (minusArray i j) := by
  intro a
  obtain ⟨g, hg, he⟩ := plus_line_all_ranks K r hr i j hij a
  refine ⟨transposeUnit K r g, transposeUnit_mem K r g hg, ?_⟩
  change (g : Mat K r).transpose = (plusArray i j a).transpose
  exact congrArg Matrix.transpose he

theorem chain_line_all_ranks (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K r) (chainArray i j) := by
  intro a
  exact ⟨(chainElement K r i j hij a).val, (chainElement K r i j hij a).property,
    chainElement_val K r i j hij a⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankRootLines
