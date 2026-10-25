import SymmetricSubgroupAsymptotics.CFSGHermitianLineIsometry
import Mathlib.Tactic.Push

/-! A nonzero nondegenerate actual subspace contains a unit-norm vector
when the coefficient automorphism is nonidentity and fixed nonzero
scalars are norms. This uses the checked all-characteristic polarization
and gives a structural section, not an isometry-order hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianUnitVectorSection
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan

variable {K I : Type*} [Field K] [Fintype I]

theorem exists_unit_norm (sigma : K ≃+* K) (H : Matrix I I K)
    (W : Submodule K (I → K)) [Nontrivial W]
    (hnonfixed : ∃ a : K, sigma a ≠ a)
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y=0) → x=0)
    (hfixed : ∀ x, sigma (hermitianPair sigma H x x)=hermitianPair sigma H x x)
    (hnorm : ∀ a : K, a ≠ 0 → sigma a=a → ∃ t : K, sigma t*t=a) :
    ∃ v ∈ W, hermitianPair sigma H v v=1 := by
  classical
  have hex : ∃ x ∈ W, hermitianPair sigma H x x ≠ 0 := by
    by_contra hh
    push_neg at hh
    have hp := (CFSGHermitianTotallyIsotropic.norm_zeroOn_iff_pair_zeroOn
      sigma hnonfixed H W).mp hh
    obtain ⟨x,hx⟩ := exists_ne (0 : W)
    apply hx
    apply Subtype.ext
    exact hND x.val x.property (fun y hy => hp x.val x.property y hy)
  obtain ⟨x,hx,hnx⟩ := hex
  have hs : sigma (hermitianPair sigma H x x)⁻¹=(hermitianPair sigma H x x)⁻¹ := by
    rw [map_inv₀,hfixed]
  obtain ⟨t,ht⟩ := hnorm (hermitianPair sigma H x x)⁻¹ (inv_ne_zero hnx) hs
  refine ⟨t • x,W.smul_mem t hx,?_⟩
  rw [hermitianPair_smul,ht,inv_mul_cancel₀ hnx]

end SymmetricSubgroupAsymptotics.FiniteHermitianUnitVectorSection
