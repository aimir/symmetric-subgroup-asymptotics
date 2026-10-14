import SymmetricSubgroupAsymptotics.ModuleGeneratorProjectionSharing

/-! Generator-position sharing persists uniformly in every submodule.
The actual acting scalar splits the intersections, so an arbitrary
submodule need not be presumed to split along an abstract direct sum. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

private def intersectionEquiv (P W : Submodule R M) :
    P.comap W.subtype ≃ₗ[R] W.comap P.subtype where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Uniform bounds on two pieces separated by an actual acting scalar
share the same generator positions in every submodule of their sum. -/
theorem uniform_of_projected_submodules
    (P Q : Submodule R M) (a : R)
    (hP : ∀ x : P, a • (x : M) = x)
    (hQ : ∀ x : Q, a • (x : M) = 0)
    (hsup : P ⊔ Q = ⊤) (n : ℕ)
    (hgenP : ∀ U : Submodule R P, ModuleGeneratedBy R U n)
    (hgenQ : ∀ U : Submodule R Q, ModuleGeneratedBy R U n)
    (W : Submodule R M) : ModuleGeneratedBy R W n := by
  let PW : Submodule R W := P.comap W.subtype
  let QW : Submodule R W := Q.comap W.subtype
  have hPW : ∀ x : PW, a • (x : W) = x := by
    intro x
    apply Subtype.ext
    exact hP ⟨x.1.1, x.2⟩
  have hQW : ∀ x : QW, a • (x : W) = 0 := by
    intro x
    apply Subtype.ext
    exact hQ ⟨x.1.1, x.2⟩
  have hsum : PW ⊔ QW = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : M) ∈ P ⊔ Q := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx
    have hap : a • (x : M) = p := by
      rw [← hpq, smul_add, hP ⟨p, hp⟩, hQ ⟨q, hq⟩, add_zero]
    have hpW : p ∈ W := hap ▸ W.smul_mem a x.property
    have hqW : q ∈ W := by
      have heq : q = (x : M) - p := by rw [← hpq, add_sub_cancel_left]
      rw [heq]
      exact W.sub_mem x.property hpW
    exact Submodule.mem_sup.mpr
      ⟨⟨p, hpW⟩, hp, ⟨q, hqW⟩, hq, Subtype.ext hpq⟩
  exact of_projected_submodules PW QW a hPW hQW hsum n
    (congr (intersectionEquiv P W).symm (hgenP _))
    (congr (intersectionEquiv Q W).symm (hgenQ _))

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
