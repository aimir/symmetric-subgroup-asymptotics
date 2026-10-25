import SymmetricSubgroupAsymptotics.ProjectiveFourSimplicity
import SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldGeneration
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Literal binary GL4, SL4 and PSL4 identifications. Simplicity is supplied
by the projective Iwasawa proof, and ordinary generation by the actual
finite-field elementary-matrix construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourLinearGroups

abbrev General := Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)
abbrev SL := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)

private theorem units_eq_one (u : (ZMod 2)ˣ) : u = 1 := by
  revert u
  decide

private def specialGeneralEquivOfUnits {n F : Type} [Fintype n] [DecidableEq n]
    [Field F] (hF : ∀ u : Fˣ, u = 1) :
    Matrix.SpecialLinearGroup n F ≃* Matrix.GeneralLinearGroup n F :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, by
      intro g
      refine ⟨⟨g.val, ?_⟩, ?_⟩
      · exact congrArg Units.val (hF g.det)
      · apply Units.ext
        rfl⟩

def specialGeneralEquiv : SL ≃* General := specialGeneralEquivOfUnits units_eq_one

theorem center_eq_bot : Subgroup.center SL = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 1
  let e : Subgroup.center SL ≃* rootsOfUnity 4 (ZMod 2) := by
    simpa only [Fintype.card_fin] using
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := ZMod 2) (0 : Fin 4))
  have hu : e ⟨z,hz⟩ = 1 := by
    apply Subtype.ext
    exact units_eq_one _
  have hz' : (⟨z,hz⟩ : Subgroup.center SL) = 1 := by
    apply e.injective
    simpa only [map_one] using hu
  exact congrArg Subtype.val hz'

def specialProjectiveEquiv : SL ≃* PSL :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL))
    ⟨(MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' (Subgroup.center SL))).mp (by
      rw [QuotientGroup.ker_mk',center_eq_bot]), QuotientGroup.mk'_surjective _⟩

theorem simple_SL : IsSimpleGroup SL := by
  letI : IsSimpleGroup PSL := ProjectiveFourSimplicity.simple
  exact specialProjectiveEquiv.isSimpleGroup

theorem simple_GL : IsSimpleGroup General := by
  letI : IsSimpleGroup SL := simple_SL
  exact specialGeneralEquiv.symm.isSimpleGroup

theorem card_GL : Nat.card General = 20160 := by
  have h := Matrix.card_GL_field (𝔽 := ZMod 2) 4
  norm_num [Fin.prod_univ_succ] at h
  simpa only [General,Nat.card_eq_fintype_card] using h

theorem genRank_GL_le_two : MarkedC4.genRank General ≤ 2 := by
  have h := CFSGTypeAFiniteFieldGeneration.genRank_le_two (F := ZMod 2) 4
    (by decide) (by omega)
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv specialGeneralEquiv).symm.le.trans h

end SymmetricSubgroupAsymptotics.BinaryFourLinearGroups
