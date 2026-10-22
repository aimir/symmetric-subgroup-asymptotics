import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernelScalar
import SymmetricSubgroupAsymptotics.CFSGEmbeddedLinearRayScalar

/-! Bilinear pairings with the same literal zero locus differ by one
nonzero scalar, provided the first pairing separates its left variable.
The proof first retains each actual functional kernel, then uses linear
ray rigidity to couple all the scalars. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGBilinearZeroLocusScalar
variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

theorem exists_nonzero_scalar (B C : U→ₗ[K]V→ₗ[K]K) (hB : Function.Injective B)
    (hne : ∃x y,B x y≠0) (hzero : ∀x y,C x y=0 ↔ B x y=0) :
    ∃c : K,c≠0 ∧ C=c•B := by
  have hpoint : ∀x : U,∃c : K,C x=c•B x := by
    intro x
    by_cases hx : x=0
    · subst x
      exact ⟨0,by rw [map_zero,map_zero,zero_smul]⟩
    have hBx : B x≠0 := by
      intro h
      exact hx (hB (h.trans B.map_zero.symm))
    have hker : (B x).ker=(C x).ker := by
      ext y
      exact (hzero x y).symm
    obtain ⟨c,_,hc⟩ := CFSGLinearFunctionalKernelScalar.exists_ne_zero_smul_of_ker_eq
      (B x) (C x) hker hBx
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := CFSGEmbeddedLinearRayScalar.exists_scalar B C hB hpoint
  have he : C=c•B := LinearMap.ext hc
  refine ⟨c,?_,he⟩
  intro hz
  obtain ⟨x,y,hxy⟩ := hne
  have hCy : C x y=0 := by rw [he,hz,zero_smul];rfl
  exact hxy ((hzero x y).mp hCy)

end SymmetricSubgroupAsymptotics.CFSGBilinearZeroLocusScalar
