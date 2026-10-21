import SymmetricSubgroupAsymptotics.CFSGSerreDiagramRootConjugacy

/-! The diagram action restricts to an automorphism of the original
root-generated group, without replacing its ambient representation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j)
include hA

theorem conjugate_mem_model (g : Ambient A K) (hg : g ∈ subgroup A K) :
    MulAut.conj (spaceEquiv A K p hA) g ∈ subgroup A K := by
  have hle : subgroup A K ≤ (subgroup A K).comap
      (MulAut.conj (spaceEquiv A K p hA)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨negative, i, t, hx⟩
    exact Subgroup.subset_closure ⟨negative, p i, t,
      conjugate_isRootElement A K p hA negative i t x hx⟩
  exact hle hg

theorem conjugate_inverse_mem_model (g : Ambient A K) (hg : g ∈ subgroup A K) :
    MulAut.conj ((spaceEquiv A K p hA)⁻¹) g ∈ subgroup A K := by
  have hle : subgroup A K ≤ (subgroup A K).comap
      (MulAut.conj ((spaceEquiv A K p hA)⁻¹)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨negative, i, t, hx⟩
    exact Subgroup.subset_closure ⟨negative, p.symm i, t,
      conjugate_inverse_isRootElement A K p hA negative i t x hx⟩
  exact hle hg

def modelAutomorphism : MulAut (Model A K) where
  toFun g := ⟨MulAut.conj (spaceEquiv A K p hA) g.val,
    conjugate_mem_model A K p hA g.val g.property⟩
  invFun g := ⟨MulAut.conj ((spaceEquiv A K p hA)⁻¹) g.val,
    conjugate_inverse_mem_model A K p hA g.val g.property⟩
  left_inv := by
    intro g
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]
  right_inv := by
    intro g
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul (MulAut.conj (spaceEquiv A K p hA)) g.val h.val

@[simp] theorem modelAutomorphism_coe (g : Model A K) :
    (modelAutomorphism A K p hA g).val =
      MulAut.conj (spaceEquiv A K p hA) g.val := rfl

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
