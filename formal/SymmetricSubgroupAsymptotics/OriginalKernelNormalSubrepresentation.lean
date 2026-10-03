import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.InducedSubrepresentationCount

/-!
# The invariant intersection in an original elementary kernel

For an extension with a literal module chart, the intersection of an
ambient normal subgroup with the elementary kernel is an invariant subspace
of the original quotient representation.  This is the exact invariant
`I = N ∩ E` retained by the affine chief-layer argument.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace OriginalKernelModuleChart

variable {p : ℕ} [Fact p.Prime]
variable {Q B : Type} [Group Q] [Group B]
variable (π : Q →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B)
variable (E : OriginalKernelModuleChart π A)

/-- The literal intersection `N ∩ ker π`, in the original kernel
coordinates, as a subrepresentation of the actual quotient action. -/
def normalSubrepresentation
    (N : Subgroup Q) [N.Normal] : Subrepresentation A.ρ where
  toSubmodule := E.normalSpace π A N
  apply_mem_toSubmodule := by
    intro b v hv
    obtain ⟨q, hq⟩ := hπ b
    obtain ⟨k, hk⟩ := E.equiv.symm.surjective (Multiplicative.ofAdd v)
    have hkv : (E.kernelCoordinates π A k).toAdd = v := by
      exact congrArg Multiplicative.toAdd hk
    have hker : (E.kernelCoordinates π A).ker ≤ N.subgroupOf π.ker := by
      intro x hx
      have hx1 : x = 1 := by
        apply E.equiv.symm.injective
        exact (MonoidHom.mem_ker.mp hx).trans (map_one E.equiv.symm).symm
      subst x
      exact Subgroup.one_mem _
    have hkN : (k : Q) ∈ N := by
      have hm : (E.kernelCoordinates π A k).toAdd ∈ E.normalSpace π A N := by
        simpa only [hkv] using hv
      exact (sectionSubgroupImage_mem_iff
        (E.kernelCoordinates π A) (N.subgroupOf π.ker) hker k).mp hm
    let k' : π.ker := MulAut.conjNormal q k
    have hk'N : (k' : Q) ∈ N := by
      exact Subgroup.Normal.conj_mem inferInstance (k : Q) hkN q
    have hcoord : (E.kernelCoordinates π A k').toAdd = A.ρ b v := by
      apply Multiplicative.ofAdd.injective
      apply E.equiv.injective
      apply Subtype.val_injective
      change (E.equiv (E.equiv.symm k') : Q) =
        (E.equiv (Multiplicative.ofAdd (A.ρ b v)) : Q)
      rw [E.equiv.apply_symm_apply]
      have hk_forward : E.equiv (Multiplicative.ofAdd v) = k := by
        rw [← hk, E.equiv.apply_symm_apply]
      rw [← hq, E.conjugate, hk_forward]
      rfl
    have hm : (E.kernelCoordinates π A k').toAdd ∈ E.normalSpace π A N :=
      (sectionSubgroupImage_mem_iff
        (E.kernelCoordinates π A) (N.subgroupOf π.ker) hker k').mpr hk'N
    simpa only [hcoord] using hm

/-- Equality of invariant intersections is exactly equality of the original
kernel intersections.  Thus the retained subrepresentation loses no
information about `I`. -/
theorem normalSubrepresentation_eq_iff_intersection_eq
    (N M : Subgroup Q) [N.Normal] [M.Normal] :
    E.normalSubrepresentation π hπ A N =
        E.normalSubrepresentation π hπ A M ↔
      N.subgroupOf π.ker = M.subgroupOf π.ker := by
  constructor
  · intro h
    apply Subgroup.ext
    intro k
    have hker : (E.kernelCoordinates π A).ker ≤ N.subgroupOf π.ker := by
      intro x hx
      have hx1 : x = 1 := by
        apply E.equiv.symm.injective
        exact (MonoidHom.mem_ker.mp hx).trans (map_one E.equiv.symm).symm
      subst x
      exact Subgroup.one_mem _
    have hker' : (E.kernelCoordinates π A).ker ≤ M.subgroupOf π.ker := by
      intro x hx
      have hx1 : x = 1 := by
        apply E.equiv.symm.injective
        exact (MonoidHom.mem_ker.mp hx).trans (map_one E.equiv.symm).symm
      subst x
      exact Subgroup.one_mem _
    have hspace : E.normalSpace π A N = E.normalSpace π A M := by
      exact congrArg Subrepresentation.toSubmodule h
    change sectionSubgroupImage (p := p) (E.kernelCoordinates π A)
        (N.subgroupOf π.ker) =
      sectionSubgroupImage (p := p) (E.kernelCoordinates π A)
        (M.subgroupOf π.ker) at hspace
    rw [← sectionSubgroupImage_mem_iff (p := p)
        (E.kernelCoordinates π A) (N.subgroupOf π.ker) hker k,
      ← sectionSubgroupImage_mem_iff (p := p)
        (E.kernelCoordinates π A) (M.subgroupOf π.ker) hker' k,
      hspace]
  · intro h
    apply Subrepresentation.toSubmodule_injective
    change E.normalSpace π A N = E.normalSpace π A M
    simpa only [normalSpace] using congrArg
      (sectionSubgroupImage (p := p) (E.kernelCoordinates π A)) h

end OriginalKernelModuleChart
end SymmetricSubgroupAsymptotics

end
