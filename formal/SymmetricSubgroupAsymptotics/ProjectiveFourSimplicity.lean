import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import SymmetricSubgroupAsymptotics.External.ProjectiveLineStabilizer
import SymmetricSubgroupAsymptotics.External.ProjectiveSpecialLinearAction
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect

/-! Simplicity of the actual four-dimensional projective special linear group.
The proof uses generic elementary generation, the Steinberg commutator identity,
and the faithful primitive projective action's Iwasawa structure. No finite
linear-group catalogue or exceptional isomorphism is used. -/
set_option autoImplicit false
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

namespace SymmetricSubgroupAsymptotics.ProjectiveFourSimplicity
open CFSGTypeAElementaryMatrices CFSGTypeAElementaryGeneration
variable {F : Type*} [Field F]

/-- Every elementary matrix is a commutator in dimension four. -/
theorem commutator_eq_top :
    commutator (SL (n := Fin 4) (F := F)) = ⊤ := by
  apply eq_top_of_elementary
  intro i j hij a
  obtain ⟨k, hik, hkj⟩ : ∃ k : Fin 4, i ≠ k ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first | contradiction | decide
  have he := elementary_commutator hik hkj hij a (1 : F)
  rw [mul_one] at he
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem elementary_mem_lineStab {i j : Fin 4} (hij : i ≠ j) (a : F) :
    elementary hij a ∈ lineStab (Submodule.span F {(Pi.single i (1 : F) : Fin 4 → F)}) := by
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
    (⨆ p : ℙ F (Fin 4 → F), lineStab p.submodule) =
      (⊤ : Subgroup (SL (n := Fin 4) (F := F))) := by
  apply eq_top_of_elementary
  intro i j hij a
  let p := Projectivization.mk F (Pi.single i (1 : F) : Fin 4 → F)
    (Pi.single_ne_zero_iff.mpr one_ne_zero)
  apply (le_iSup (fun p : ℙ F (Fin 4 → F) => lineStab p.submodule) p)
  change elementary hij a ∈ lineStab
    (Projectivization.mk F _ _).submodule
  rw [Projectivization.submodule_mk]
  exact elementary_mem_lineStab hij a

private theorem iSup_iwasawaT_eq_top :
    iSup (PSL.iwasawaT (F := F) (ι := Fin 4)) = ⊤ := by
  change (⨆ p : ℙ F (Fin 4 → F),
    (lineStab p.submodule).map (QuotientGroup.mk' _)) = ⊤
  rw [← Subgroup.map_iSup, iSup_lineStab_eq_top]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- The classical projective action's Iwasawa structure. -/
noncomputable def iwasawa :
    MulAction.IwasawaStructure (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F)
      (ℙ F (Fin 4 → F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 4) p.submodule) := by
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
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) := by
  let g : SL (n := Fin 4) (F := F) := elementary (by decide : (0 : Fin 4) ≠ 1) 1
  have hnot : g ∉ Subgroup.center (SL (n := Fin 4) (F := F)) := by
    intro h
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have he := congrFun (congrFun hr 0) 1
    simp [g, elementary, Matrix.transvection, Matrix.scalar] at he
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup (Fin 4) F),
    1, fun h => hnot ?_⟩⟩
  exact (QuotientGroup.eq_one_iff _).mp h

/-- The projective special linear group of dimension four is simple over
any field, without a finite-field exception. -/
theorem simple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) := by
  letI : Group.IsPerfect (SL (n := Fin 4) (F := F)) := ⟨commutator_eq_top⟩
  letI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) := projective_nontrivial
  exact MulAction.IwasawaStructure.isSimpleGroup
    (Group.IsPerfect.commutator_eq_top (G := Matrix.ProjectiveSpecialLinearGroup (Fin 4) F))
    iwasawa inferInstance

end SymmetricSubgroupAsymptotics.ProjectiveFourSimplicity
