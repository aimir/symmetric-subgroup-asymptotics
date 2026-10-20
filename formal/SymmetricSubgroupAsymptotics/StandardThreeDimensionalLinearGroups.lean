import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Field.ZMod

/-! Standard linear models for the small affine complements.
The only external mathematical premise is classical ProjectiveThree simplicity; all
centers, determinant maps and orders below are internal algebra.
Source: Jordan--Dickson simplicity, as proved in Keith Conrad,
*Simplicity of PSL_n(F)*, Section4 (n>2),
https://kconrad.math.uconn.edu/blurbs/grouptheory/PSLnsimple.pdf.
This is not a finite-affine composition or catalogue receipt. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups

abbrev GeneralThree (p : ℕ) := Matrix.GeneralLinearGroup (Fin 3) (ZMod p)
abbrev SpecialThree (p : ℕ) := Matrix.SpecialLinearGroup (Fin 3) (ZMod p)
abbrev ProjectiveThree (p : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p)

/-- Two specializations of ordinary projective-linear simplicity. -/
def PublishedSimplicity : Prop := IsSimpleGroup (ProjectiveThree 2) ∧ IsSimpleGroup (ProjectiveThree 3)

variable (p : ℕ) [Fact p.Prime]

/-- The determinant-one subgroup is literally SpecialThree, with the same matrices. -/
def specialLinearKerEquiv : SpecialThree p ≃* (Matrix.GeneralLinearGroup.det : GeneralThree p →* (ZMod p)ˣ).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g, Matrix.SpecialLinearGroup.coeToGL_det g⟩
  invFun g := ⟨g.val.val, by
    have h := g.property
    change Matrix.GeneralLinearGroup.det g.val = 1 at h
    exact congrArg Units.val h⟩
  left_inv g := Subtype.ext rfl
  right_inv g := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' g h := by apply Subtype.ext; apply Units.ext; rfl

/-- Cubic roots in the scalar units control the actual center. -/
theorem center_eq_bot_of_units_cube (hcube : ∀ u : (ZMod p)ˣ, u ^ 3 = u) :
    Subgroup.center (SpecialThree p) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 1
  let e : Subgroup.center (SpecialThree p) ≃* rootsOfUnity 3 (ZMod p) := by
    simpa only [Fintype.card_fin] using
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := ZMod p) (0 : Fin 3))
  have hu : e ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    exact (hcube (e ⟨z, hz⟩).val).symm.trans
      ((mem_rootsOfUnity 3 _).mp (e ⟨z, hz⟩).property)
  have hz' : (⟨z, hz⟩ : Subgroup.center (SpecialThree p)) = 1 := by
    apply e.injective
    simpa only [map_one] using hu
  exact congrArg Subtype.val hz'

/-- For these fields no projective scalar quotient changes SpecialThree. -/
def specialLinearProjectiveEquiv (hcube : ∀ u : (ZMod p)ˣ, u ^ 3 = u) :
    SpecialThree p ≃* ProjectiveThree p :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (SpecialThree p)))
    ⟨(MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' (Subgroup.center (SpecialThree p)))).mp (by
      rw [QuotientGroup.ker_mk', center_eq_bot_of_units_cube p hcube]),
      QuotientGroup.mk'_surjective _⟩

local instance standardThreePrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance standardThreePrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem units_two_eq_one : ∀ u : (ZMod 2)ˣ, u = 1 := by decide

theorem units_two_cube : ∀ u : (ZMod 2)ˣ, u ^ 3 = u := by decide

theorem units_three_cube : ∀ u : (ZMod 3)ˣ, u ^ 3 = u := by decide

/-- In characteristic two the full determinant target is trivial. -/
def specialLinearGeneralTwoEquiv : SpecialThree 2 ≃* GeneralThree 2 :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, by
      intro g
      refine ⟨⟨g.val, ?_⟩, ?_⟩
      · exact congrArg Units.val (units_two_eq_one g.det)
      · apply Units.ext
        rfl⟩

theorem simple_SL_two (h : PublishedSimplicity) : IsSimpleGroup (SpecialThree 2) := by
  letI : IsSimpleGroup (ProjectiveThree 2) := h.1
  exact (specialLinearProjectiveEquiv 2 units_two_cube).isSimpleGroup

theorem simple_SL_three (h : PublishedSimplicity) : IsSimpleGroup (SpecialThree 3) := by
  letI : IsSimpleGroup (ProjectiveThree 3) := h.2
  exact (specialLinearProjectiveEquiv 3 units_three_cube).isSimpleGroup

theorem simple_GL_two (h : PublishedSimplicity) : IsSimpleGroup (GeneralThree 2) := by
  letI : IsSimpleGroup (SpecialThree 2) := simple_SL_two h
  exact specialLinearGeneralTwoEquiv.symm.isSimpleGroup

theorem card_GL_two : Nat.card (GeneralThree 2) = 168 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 2) 3
  norm_num [Fin.prod_univ_succ] at h
  simpa only [GeneralThree, Nat.card_eq_fintype_card] using h

theorem card_GL_three : Nat.card (GeneralThree 3) = 11232 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 3) 3
  norm_num [Fin.prod_univ_succ] at h
  simpa only [GeneralThree, Nat.card_eq_fintype_card] using h

theorem card_SL_two : Nat.card (SpecialThree 2) = 168 := by
  rw [Nat.card_congr specialLinearGeneralTwoEquiv.toEquiv, card_GL_two]

end SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
