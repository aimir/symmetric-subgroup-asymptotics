import SymmetricSubgroupAsymptotics.CFSGOrthogonalBConjugateRootPlanes
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicRootLines

/-! The natural two-plane label is independent of the chosen original
conjugator representing a literal root subgroup. No classification or
surjectivity onto all polar two-planes is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

theorem conjugateRootPlane_eq_of_rootLine_eq (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3))
    (hL : conjugateRootLine (K := K) h2 s g = conjugateRootLine (K := K) h2 s h) :
    conjugateRootPlane (K := K) s g = conjugateRootPlane (K := K) s h := by
  have hx : g * highestRoot (K := K) s 1 * g⁻¹ ∈ conjugateRootLine (K := K) h2 s g :=
    by
      have hbase : highestRoot (K := K) s 1 ∈ highestRootLine h2 s :=
        (mem_highestRootLine_iff h2 s (highestRoot (K := K) s 1)).mpr ⟨1, rfl⟩
      exact ⟨highestRoot (K := K) s 1, hbase, rfl⟩
  rw [hL] at hx
  obtain ⟨u, hu, he⟩ := hx
  obtain ⟨b, hb⟩ := (mem_highestRootLine_iff h2 s u).mp hu
  have he' : h * highestRoot (K := K) s b * h⁻¹ = g * highestRoot (K := K) s 1 * g⁻¹ := by
    change h * u * h⁻¹ = g * highestRoot (K := K) s 1 * g⁻¹ at he
    simpa only [hb] using he
  have hroot : highestRoot (K := K) s 1 ≠ 1 := by
    intro hz
    exact one_ne_zero (highestRoot_injective h2 s (hz.trans (highestRoot_zero h2 s).symm))
  have hnon : g * highestRoot (K := K) s 1 * g⁻¹ ≠ 1 := by
    intro hz
    exact hroot ((MulAut.conj g).injective (hz.trans (MulAut.conj g).map_one.symm))
  have hb0 : b ≠ 0 := by
    intro hz
    apply hnon
    rw [← he', hz, highestRoot_zero h2 s, mul_one, mul_inv_cancel]
  calc
    conjugateRootPlane (K := K) s g = LinearMap.range (Matrix.mulVecLin
        (((g * highestRoot (K := K) s 1 * g⁻¹).val : Mat K (s + 3)) - 1)) :=
      (conjugate_highestRoot_displacement_range h2 s g 1 one_ne_zero).symm
    _ = LinearMap.range (Matrix.mulVecLin
        (((h * highestRoot (K := K) s b * h⁻¹).val : Mat K (s + 3)) - 1)) :=
      congrArg (fun u : elementaryRootGroup K (s + 3) =>
        LinearMap.range (Matrix.mulVecLin ((u.val : Mat K (s + 3)) - 1))) he'.symm
    _ = conjugateRootPlane (K := K) s h := conjugate_highestRoot_displacement_range h2 s h b hb0

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
