import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! A Sylow subgroup meets every normal subgroup in a Sylow subgroup.
The construction conjugates a Sylow of the normal subgroup inside the
ambient finite group; it does not require containment of the ambient Sylow. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteSylowNormalIntersection
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_sylow_comap (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ Q : Sylow p N, (Q : Subgroup N) = (P : Subgroup G).comap N.subtype := by
  let Q : Sylow p N := Sylow.nonempty.some
  obtain ⟨R, hR⟩ := Q.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  let a : MulAut N := MulAut.conjNormal g
  refine ⟨Q.mapSurjective (f := a.toMonoidHom) a.surjective, ?_⟩
  have hP : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = (P : Subgroup G) := by
    exact congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
  change (Q : Subgroup N).map a.toMonoidHom = _
  rw [Subgroup.map_equiv_eq_comap_symm', ← hR]
  rw [Subgroup.map_equiv_eq_comap_symm'] at hP
  rw [← hP]
  ext x
  change ((MulAut.conjNormal g).symm x : G) ∈ (R : Subgroup G) ↔
    (MulAut.conj g).symm (x : G) ∈ (R : Subgroup G)
  rw [MulAut.conjNormal_symm_apply, MulAut.conj_symm_apply]

def normalIntersection (P : Sylow p G) (N : Subgroup G) [N.Normal] : Sylow p N :=
  (exists_sylow_comap P N).choose

theorem normalIntersection_coe (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (normalIntersection P N : Subgroup N) = (P : Subgroup G).comap N.subtype :=
  (exists_sylow_comap P N).choose_spec

end SymmetricSubgroupAsymptotics.FiniteSylowNormalIntersection
