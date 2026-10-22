import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! Two nonzero linear functionals with the same kernel differ by a
nonzero scalar. The proof retains an actual normalized vector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernelScalar
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_ne_zero_smul_of_ker_eq (f g : V→ₗ[K]K)
    (hker : f.ker=g.ker) (hf : f≠0) : ∃c : K,c≠0 ∧ g=c•f := by
  classical
  obtain ⟨u,hu⟩ : ∃u,f u≠0 := by
    by_contra hn
    apply hf
    ext u
    by_contra hx
    exact hn ⟨u,hx⟩
  let v := (f u)⁻¹•u
  have hv : f v=1 := by simp [v,hu]
  have hgv : g v≠0 := by
    intro hz
    have hm : v∈g.ker := hz
    rw [←hker] at hm
    have hh : f v=0 := hm
    rw [hv] at hh
    exact one_ne_zero hh
  refine ⟨g v,hgv,?_⟩
  ext x
  have hh : f (x-f x•v)=0 := by
    rw [map_sub,map_smul,hv,smul_eq_mul,mul_one,sub_self]
  have hm : x-f x•v∈f.ker := hh
  rw [hker] at hm
  have hg : g (x-f x•v)=0 := hm
  rw [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at hg
  change g x=g v*f x
  exact hg.trans (mul_comm _ _)

end SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernelScalar
