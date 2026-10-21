import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Distinct joint characters force every joint eigenvector to lie on
one of the original basis lines. Normality then makes the ambient
group permute those lines. No classification of linear groups occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SeparatedEigenbasisMonomial

variable {k G V I : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (b : Module.Basis I k V)
    (N : Subgroup G) (a : N → I → k)
    (heigen : ∀ (n : N) (i : I),rho n.val (b i)=a n i • b i)

include heigen

theorem coordinate (n : N) (v : V) (j : I) :
    b.repr (rho n.val v) j=a n j*b.repr v j := by
  have he : (b.coord j).comp (rho n.val)=a n j • b.coord j := by
    apply b.ext
    intro i
    by_cases hi : i=j
    · subst i
      simp [heigen,Module.Basis.coord_apply]
    · simp [heigen,Module.Basis.coord_apply,hi]
  exact congrArg (fun f : V →ₗ[k] k => f v) he

theorem eigenvector_is_basis_line
    (hsep : ∀ i j : I,i≠j → ∃ n : N,a n i≠a n j)
    (v : V) (hv : v≠0)
    (hjoint : ∀ n : N,∃ c : k,rho n.val v=c • v) :
    ∃ (j : I) (c : k),c≠0 ∧ v=c • b j := by
  have hex : ∃ j : I,b.repr v j≠0 := by
    by_contra h
    apply hv
    apply b.repr.injective
    apply Finsupp.ext
    intro j
    simpa using not_not.mp (not_exists.mp h j)
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,b.repr v j,hj,?_⟩
  apply b.ext_elem_iff.mpr
  intro i
  by_cases hij : i=j
  · subst i
    simp
  · have hi : b.repr v i=0 := by
      by_contra hi
      obtain ⟨n,hn⟩ := hsep i j hij
      obtain ⟨c,hc⟩ := hjoint n
      have he (t : I) : a n t*b.repr v t=c*b.repr v t := by
        rw [←coordinate rho b N a heigen n v t,hc]
        simp
      exact hn ((mul_right_cancel₀ hi (he i)).trans (mul_right_cancel₀ hj (he j)).symm)
    simp [hi,Ne.symm hij]

variable [N.Normal]

theorem normal_action_is_monomial
    (hsep : ∀ i j : I,i≠j → ∃ n : N,a n i≠a n j)
    (g : G) (i : I) :
    ∃ (j : I) (c : k),c≠0 ∧ rho g (b i)=c • b j := by
  have hv : rho g (b i)≠0 := by
    intro hz
    have he := congrArg (rho g⁻¹) hz
    have hleft : rho g⁻¹ (rho g (b i))=b i := by
      change (rho g⁻¹*rho g) (b i)=b i
      rw [←map_mul,inv_mul_cancel,map_one]
      rfl
    rw [hleft,map_zero] at he
    exact b.ne_zero i he
  apply eigenvector_is_basis_line rho b N a heigen hsep _ hv
  intro n
  let m : N := ⟨g⁻¹*n.val*g,by
    simpa only [inv_inv] using Subgroup.Normal.conj_mem (inferInstance : N.Normal)
      n.val n.property g⁻¹⟩
  refine ⟨a m i,?_⟩
  have he : n.val*g=g*m.val := by
    dsimp only [m]
    simp only [mul_assoc,mul_inv_cancel_left]
  calc
    _=rho (n.val*g) (b i) := by rw [map_mul]; rfl
    _=rho (g*m.val) (b i) := by rw [he]
    _=rho g (rho m.val (b i)) := by rw [map_mul]; rfl
    _=a m i • rho g (b i) := by rw [heigen,map_smul]

end SymmetricSubgroupAsymptotics.SeparatedEigenbasisMonomial
