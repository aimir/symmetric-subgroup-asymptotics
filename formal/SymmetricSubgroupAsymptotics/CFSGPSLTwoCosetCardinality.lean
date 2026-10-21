import SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
import SymmetricSubgroupAsymptotics.CFSGRankOneTwoCellCardinality

/-! The original PSL2 Borel has index q+1, derived from its actual
two-cell cover and actual root size. No pre-existing PSL order formula
or small-field group identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open Matrix CFSGTypeASLTwoWeyl CFSGSLTwoUpperRoots
open CFSGPSLTwoRootCoordinates
variable {F : Type*} [Field F]

theorem projectiveBorel_inf_opposite_root :
    projectiveBorel (F:=F) ⊓ (projectiveRoot (F:=F)).map
      (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom=⊥ := by
  apply bot_unique
  rintro _ ⟨hx,u,hu,rfl⟩
  obtain ⟨a,rfl⟩ := hu
  change projectiveWeyl*projectiveUpper a.toAdd*(projectiveWeyl (F:=F))⁻¹∈
    projectiveBorel at hx
  rw [projective_weyl_upper] at hx
  have hh := (projection_mem_borel_iff (lower (-a.toAdd))).mp hx
  change (lower (-a.toAdd)).val 1 0=0 at hh
  have ha : a.toAdd=0 := by
    simpa [lower,CFSGTypeAElementaryMatrices.elementary,
      Matrix.transvection,Matrix.single_apply,Matrix.one_apply] using hh
  change projectiveWeyl*projectiveUpper a.toAdd*(projectiveWeyl (F:=F))⁻¹=1
  rw [ha,projectiveUpper_zero,mul_one,mul_inv_cancel]

theorem projectiveRoot_card : Nat.card (projectiveRoot (F:=F))=Nat.card F := by
  let e : Multiplicative F ≃ F :=
    { toFun := Multiplicative.toAdd
      invFun := Multiplicative.ofAdd
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr (projectiveRootEquiv (F:=F)).symm.toEquiv).trans (Nat.card_congr e)

theorem projective_card_eq_borel_mul [Finite F] :
    Nat.card (PSL (F:=F))=Nat.card (projectiveBorel (F:=F))*(1+Nat.card F) := by
  have hh := CFSGRankOneTwoCellCardinality.card_eq
    (projectiveBorel (F:=F)) (projectiveRoot (F:=F)) projectiveWeyl
    projectiveRoot_le_borel projectiveWeyl_not_mem_borel
    projectiveBorel_inf_opposite_root two_cells
  rwa [projectiveRoot_card] at hh

theorem projectiveBorel_index [Finite F] :
    (projectiveBorel (F:=F)).index=Nat.card F+1 := by
  have hc := (projectiveBorel (F:=F)).card_mul_index
  rw [projective_card_eq_borel_mul] at hc
  have hi := Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := projectiveBorel (F:=F))) hc
  simpa only [Nat.add_comm] using hi

theorem points_card [Finite F] : Nat.card (Points (F:=F))=Nat.card F+1 := by
  rw [←Subgroup.index_eq_card,projectiveBorel_index]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
