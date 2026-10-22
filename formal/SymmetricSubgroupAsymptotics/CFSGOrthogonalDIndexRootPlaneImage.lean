import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneRootLine

/-! The SAME nonidentity D highest-root displacement has the actual
positive two-plane as its image, in all characteristics. Conjugate
root-subgroup equality therefore determines its original natural plane.
Together with the reverse pair-operator theorem this is an exact label,
not a recognition assumption or an abstract point action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexHighestRoot CFSGOrthogonalDIndexUnipotentCenter
open CFSGOrthogonalDIndexFlagVectors CFSGOrthogonalDIndexPositiveCentralizer
open CFSGOrthogonalDIndexPairOperator CFSGOrthogonalDIndexPlaneRootLine
variable (K : Type) [Field K]

def standardRootPlane (s : ℕ) : Submodule K (Index (s + 4) → K) :=
  Submodule.span K {firstVector K s, secondVector K s}

theorem highestRoot_injective (s : ℕ) : Function.Injective (highestRoot K s) := by
  intro a b h
  exact highestInU_injective K s (Subtype.ext h)

theorem highestRoot_zero (s : ℕ) : highestRoot K s 0 = 1 :=
  congrArg Subtype.val (highestInU_zero K s)

theorem highestRoot_displacement (s : ℕ) (a : K) (v : Index (s + 4) → K) :
    (((highestRoot K s a).val : Mat K (s + 4)) - 1) *ᵥ v =
      (a * v (Sum.inr (secondIndex s))) • firstVector K s -
        (a * v (Sum.inr 0)) • secondVector K s := by
  change (((highestInU K s a).val.val : Mat K (s + 4)) - 1) *ᵥ v = _
  rw [highestInU_val, add_sub_cancel_left, Matrix.smul_mulVec, highestDirection,
    pairedUpper, Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec]
  funext x
  simp only [Pi.smul_apply, Pi.sub_apply, firstVector, secondVector, Pi.single_apply,
    Function.update_apply, Pi.zero_apply, smul_eq_mul]
  split_ifs <;> ring

theorem highestRoot_displacement_range (s : ℕ) (a : K) (ha : a ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (((highestRoot K s a).val : Mat K (s + 4)) - 1)) =
      standardRootPlane K s := by
  have h0 : firstVector K s ∈ standardRootPlane K s :=
    Submodule.subset_span (Or.inl rfl)
  have h1 : secondVector K s ∈ standardRootPlane K s :=
    Submodule.subset_span (Or.inr rfl)
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, highestRoot_displacement]
    exact (standardRootPlane K s).sub_mem
      ((standardRootPlane K s).smul_mem _ h0) ((standardRootPlane K s).smul_mem _ h1)
  · apply Submodule.span_le.mpr
    rintro y (hy | hy)
    · subst y
      refine ⟨a⁻¹ • Pi.single (Sum.inr (secondIndex s)) (1 : K), ?_⟩
      rw [Matrix.mulVecLin_apply, highestRoot_displacement]
      simp [Pi.single_apply, firstVector, secondVector, secondIndex, Fin.ext_iff,
        smul_eq_mul, mul_inv_cancel₀ ha]
    · rcases hy with rfl
      refine ⟨(-a⁻¹) • Pi.single (Sum.inr (0 : Fin (s + 4))) (1 : K), ?_⟩
      rw [Matrix.mulVecLin_apply, highestRoot_displacement]
      simp [Pi.single_apply, firstVector, secondVector, secondIndex, Fin.ext_iff,
        smul_eq_mul, mul_inv_cancel₀ ha, mul_neg]

theorem conjugate_highestRoot_displacement_range (s : ℕ)
    (g : elementaryRootGroup K (s + 4)) (a : K) (ha : a ≠ 0) :
    LinearMap.range (Matrix.mulVecLin
      (((g * highestRoot K s a * g⁻¹).val : Mat K (s + 4)) - 1)) =
        conjugateRootPlane K s g := by
  change LinearMap.range (Matrix.mulVecLin
    (((g.val * (highestRoot K s a).val * g.val⁻¹ : (Mat K (s + 4))ˣ) : Mat K (s + 4)) - 1)) = _
  rw [CFSGMatrixConjugateDisplacement.conjugate_sub_one,
    CFSGMatrixConjugateDisplacement.conjugate_range, highestRoot_displacement_range K s a ha]
  rw [standardRootPlane, Submodule.map_span, Set.image_pair]
  rfl

theorem conjugateRootPlane_eq_of_rootLine_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hL : conjugateRootLine K s g = conjugateRootLine K s h) :
    conjugateRootPlane K s g = conjugateRootPlane K s h := by
  have hx : g * highestRoot K s 1 * g⁻¹ ∈ conjugateRootLine K s g :=
    ⟨highestRoot K s 1, (mem_highestRootLine_iff K s _).mpr ⟨1, rfl⟩, rfl⟩
  rw [hL] at hx
  obtain ⟨u, hu, he⟩ := hx
  obtain ⟨b, hb⟩ := (mem_highestRootLine_iff K s u).mp hu
  have he' : h * highestRoot K s b * h⁻¹ = g * highestRoot K s 1 * g⁻¹ := by
    change h * u * h⁻¹ = g * highestRoot K s 1 * g⁻¹ at he
    simpa only [hb] using he
  have hroot : highestRoot K s 1 ≠ 1 := by
    intro hz
    exact one_ne_zero (highestRoot_injective K s (hz.trans (highestRoot_zero K s).symm))
  have hnon : g * highestRoot K s 1 * g⁻¹ ≠ 1 := by
    intro hz
    exact hroot ((MulAut.conj g).injective (hz.trans (MulAut.conj g).map_one.symm))
  have hb0 : b ≠ 0 := by
    intro hz
    apply hnon
    rw [← he', hz, highestRoot_zero, mul_one, mul_inv_cancel]
  calc
    conjugateRootPlane K s g = LinearMap.range (Matrix.mulVecLin
        (((g * highestRoot K s 1 * g⁻¹).val : Mat K (s + 4)) - 1)) :=
      (conjugate_highestRoot_displacement_range K s g 1 one_ne_zero).symm
    _ = LinearMap.range (Matrix.mulVecLin
        (((h * highestRoot K s b * h⁻¹).val : Mat K (s + 4)) - 1)) :=
      congrArg (fun u : elementaryRootGroup K (s + 4) =>
        LinearMap.range (Matrix.mulVecLin ((u.val : Mat K (s + 4)) - 1))) he'.symm
    _ = conjugateRootPlane K s h := conjugate_highestRoot_displacement_range K s h b hb0

theorem conjugateRootLine_eq_iff_plane_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) :
    conjugateRootLine K s g = conjugateRootLine K s h ↔
      conjugateRootPlane K s g = conjugateRootPlane K s h :=
  ⟨conjugateRootPlane_eq_of_rootLine_eq K s g h, conjugateRootLine_eq_of_plane_eq K s g h⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootPlaneImage
