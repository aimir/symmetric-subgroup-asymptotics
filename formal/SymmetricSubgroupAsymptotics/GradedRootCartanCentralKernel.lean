import SymmetricSubgroupAsymptotics.LiteralGradedMatrixKernelDetection
import Mathlib.Algebra.Lie.OfAssociative

/-! Centrality of the matrix-realization kernel from a genuine root/Cartan
basis. Root coefficients are isolated by literal disjoint lattice degrees,
then detected by a separately proved unit-bracket identity. This is an
internal algebraic assembly lemma, not an exceptional-recognition input. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.GradedRootCartanCentralKernel
attribute [local instance 100] LieRing.ofAssociativeRing
open CFSGGradedMatrixSupport LiteralGradedMatrixKernelDetection

/-- All data refer to the SAME source basis and SAME matrix Lie map.
The Cartan part may have a nonzero realization kernel; it is proved
central rather than discarded or assumed faithful. -/
theorem kernel_is_central
    {R L I J K W : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [AddCommGroup W]
    (b : Module.Basis (J ⊕ K) R L) (phi : L →ₗ⁅R⁆ Matrix I I R)
    (weight : I → W) (degree : J → W) (hinj : Function.Injective degree)
    (hne : ∀ a, degree a ≠ 0)
    (hroot : ∀ a, Supported weight (fun w => w + degree a) (phi (b (.inl a))))
    (hcartan : ∀ i, Supported weight id (phi (b (.inr i))))
    (omega : K → J → R)
    (hweight : ∀ i a, ⁅b (.inr i), b (.inl a)⁆ = omega i a • b (.inl a))
    (hcomm : ∀ i j, ⁅b (.inr i), b (.inr j)⁆ = 0)
    (hdetect : ∀ (a : J) (c : R), c • phi (b (.inl a)) = 0 → c = 0)
    (z : L) (hz : phi z = 0) : ∀ y : L, ⁅z, y⁆ = 0 := by
  classical
  let c : J → R := fun a => b.repr z (.inl a)
  let d : K → R := fun i => b.repr z (.inr i)
  have hdecomp : z = (∑ a, c a • b (.inl a)) + ∑ i, d i • b (.inr i) := by
    have h := b.sum_repr z
    rw [Fintype.sum_sum_type] at h
    exact h.symm
  have hC : Supported weight id (∑ i, d i • phi (b (.inr i))) := by
    intro u v huv
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [hcartan i u v huv, smul_zero]
  have hsum : (∑ a, c a • phi (b (.inl a))) +
      (∑ i, d i • phi (b (.inr i))) = 0 := by
    have h := congrArg phi hdecomp
    simp only [map_add, map_sum, map_smul] at h
    exact h.symm.trans hz
  have hc (a : J) : c a = 0 :=
    hdetect a (c a) (component_smul_eq_zero weight degree hinj hne
      (fun a => phi (b (.inl a))) hroot _ hC c hsum a)
  have hcart : z = ∑ i, d i • b (.inr i) := by
    simpa only [hc, zero_smul, Finset.sum_const_zero, zero_add] using hdecomp
  have hzroot (a : J) : ⁅z, b (.inl a)⁆ = 0 := by
    have hb : ⁅z, b (.inl a)⁆ = (∑ i, d i * omega i a) • b (.inl a) := by
      rw [hcart, sum_lie]
      simp only [smul_lie, hweight, smul_smul]
      rw [Finset.sum_smul]
    have hzero : (∑ i, d i * omega i a) • phi (b (.inl a)) = 0 := by
      rw [← map_smul, ← hb, LieHom.map_lie, hz, zero_lie]
    rw [hb, hdetect a _ hzero, zero_smul]
  have hzcart (j : K) : ⁅z, b (.inr j)⁆ = 0 := by
    rw [hcart, sum_lie]
    simp only [smul_lie, hcomm, smul_zero, Finset.sum_const_zero]
  intro y
  rw [← b.sum_repr y, lie_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [lie_smul]
  cases j with
  | inl a => rw [hzroot, smul_zero]
  | inr i => rw [hzcart, smul_zero]

end SymmetricSubgroupAsymptotics.GradedRootCartanCentralKernel
