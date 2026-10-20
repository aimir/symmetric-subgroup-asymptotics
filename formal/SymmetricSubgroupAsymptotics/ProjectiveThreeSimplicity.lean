import SymmetricSubgroupAsymptotics.SLThreeElementaryGeneration
import SymmetricSubgroupAsymptotics.External.ProjectiveLineStabilizer
import SymmetricSubgroupAsymptotics.External.ProjectiveSpecialLinearAction
import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect

/-!
# Simplicity of PSL(3) without ATLAS code

The elementary matrices generate SL(3) and are commutators.  The unipotent
radicals of projective-point stabilizers are abelian, conjugate naturally,
and generate.  The faithful primitive projective action therefore satisfies
mathlib's Iwasawa criterion.  This proves simplicity over every field and
then supplies the two small-field instances used in T1.

The elementary generation and commutator proof is written in this project;
the action and line-stabilizer lemmas are Apache-licensed mathlib backports.
No ATLAS definitions, certificates, or proofs are imported.
-/
set_option autoImplicit false
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

namespace SymmetricSubgroupAsymptotics.ProjectiveThreeSimplicity
open SLThreeElementary
variable {F : Type*} [Field F]

private theorem elementary_mem_lineStab {i j : Fin 3} (hij : i ≠ j) (a : F) :
    elementary hij a ∈ lineStab (Submodule.span F {(Pi.single i (1 : F) : Fin 3 → F)}) := by
  intro w
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a * w j, ?_⟩
  simp [Matrix.SpecialLinearGroup.smul_def, elementary, Matrix.transvection,
    add_smul, Matrix.single_mulVec, mul_smul]
  ext k
  by_cases hk : k = i
  · subst k; simp
  · simp [hk]

/-- Projective-point radicals generate the special linear group. -/
theorem iSup_lineStab_eq_top :
    (⨆ p : ℙ F (Fin 3 → F), lineStab p.submodule) =
      (⊤ : Subgroup (SL (F := F))) := by
  apply eq_top_of_elementary
  intro i j hij a
  let p := Projectivization.mk F (Pi.single i (1 : F) : Fin 3 → F)
    (Pi.single_ne_zero_iff.mpr one_ne_zero)
  apply (le_iSup (fun p : ℙ F (Fin 3 → F) => lineStab p.submodule) p)
  change elementary hij a ∈ lineStab
    (Projectivization.mk F _ _).submodule
  rw [Projectivization.submodule_mk]
  exact elementary_mem_lineStab hij a

private theorem iSup_iwasawaT_eq_top :
    iSup (PSL.iwasawaT (F := F) (ι := Fin 3)) = ⊤ := by
  change (⨆ p : ℙ F (Fin 3 → F),
    (lineStab p.submodule).map (QuotientGroup.mk' _)) = ⊤
  rw [← Subgroup.map_iSup, iSup_lineStab_eq_top]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- The classical projective action's Iwasawa structure. -/
noncomputable def iwasawa :
    MulAction.IwasawaStructure (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
      (ℙ F (Fin 3 → F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 3) p.submodule) := by
      rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨gSL, rfl⟩ := QuotientGroup.mk_surjective g
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    change Subgroup.map _ _ = _
    rw [PSL.smul_submodule, Matrix.SpecialLinearGroup.lineStab_smul,
      PSL.iwasawaT_map_conj]
  is_generator := iSup_iwasawaT_eq_top

private theorem projective_nontrivial :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  let g : SL (F := F) := elementary (by decide : (0 : Fin 3) ≠ 1) 1
  have hnot : g ∉ Subgroup.center (SL (F := F)) := by
    intro h
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have he := congrFun (congrFun hr 0) 1
    simp [g, elementary, Matrix.transvection, Matrix.scalar] at he
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F),
    1, fun h => hnot ?_⟩⟩
  exact (QuotientGroup.eq_one_iff _).mp h

/-- The projective special linear group of dimension three is simple over
any field, including the two small fields needed by the affine catalogue. -/
theorem simple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  letI : Group.IsPerfect (SL (F := F)) := ⟨SLThreeElementary.commutator_eq_top⟩
  letI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := projective_nontrivial
  exact MulAction.IwasawaStructure.isSimpleGroup
    (Group.IsPerfect.commutator_eq_top (G := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    iwasawa inferInstance

/-- The former two-instance literature input is completely discharged. -/
theorem proved : StandardThreeDimensionalLinearGroups.PublishedSimplicity := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact ⟨simple, simple⟩

end SymmetricSubgroupAsymptotics.ProjectiveThreeSimplicity
