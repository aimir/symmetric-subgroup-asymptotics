import SymmetricSubgroupAsymptotics.CFSGSerreDiagramRootConjugacy
import SymmetricSubgroupAsymptotics.CFSGSerreFieldTensor

/-! Composition of the actual field-tensor action and actual integral
diagram action on the original elementary model. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j) (σ : K ≃+* K)
include hA

def ambientAutomorphism : MulAut (Ambient A K) :=
  (CFSGSerreField.ambientAutomorphism A K σ).trans
    (MulAut.conj (CFSGSerreDiagram.spaceEquiv A K p hA))

theorem ambientAutomorphism_isRootElement (negative : Bool) (i : Fin n) (t : K)
    (g : Ambient A K) (hg : IsRootElement A K negative i t g) :
    IsRootElement A K negative (p i) (σ t) (ambientAutomorphism A K p hA σ g) := by
  exact CFSGSerreDiagram.conjugate_isRootElement A K p hA negative i (σ t) _
    (CFSGSerreField.ambientAutomorphism_isRootElement A K σ negative i t g hg)

theorem conjugate_model_eq :
    (subgroup A K).map (ambientAutomorphism A K p hA σ).toMonoidHom = subgroup A K := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨negative, i, t, hg⟩
    exact Subgroup.subset_closure ⟨negative, p i, σ t,
      ambientAutomorphism_isRootElement A K p hA σ negative i t g hg⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨negative, i, t, hg⟩
    let u := rootEquiv A K negative (p.symm i) (σ.symm t)
    have hu : u ∈ subgroup A K := rootEquiv_mem_model A K negative (p.symm i) (σ.symm t)
    have he : ambientAutomorphism A K p hA σ u = g := by
      apply LinearEquiv.toLinearMap_injective
      have hr := ambientAutomorphism_isRootElement A K p hA σ negative
        (p.symm i) (σ.symm t) u (rootEquiv_isRootElement A K negative (p.symm i) (σ.symm t))
      have hr' : (ambientAutomorphism A K p hA σ u).toLinearMap =
          rootOperator A K negative i t := by
        simpa only [Equiv.apply_symm_apply, RingEquiv.apply_symm_apply] using hr
      exact hr'.trans hg.symm
    exact ⟨u, hu, he⟩

def modelAutomorphism : MulAut (Model A K) :=
  ((ambientAutomorphism A K p hA σ).subgroupMap (subgroup A K)).trans
    (MulEquiv.subgroupCongr (conjugate_model_eq A K p hA σ))

@[simp] theorem modelAutomorphism_coe (g : Model A K) :
    (modelAutomorphism A K p hA σ g).val = ambientAutomorphism A K p hA σ g.val := rfl

end SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram
