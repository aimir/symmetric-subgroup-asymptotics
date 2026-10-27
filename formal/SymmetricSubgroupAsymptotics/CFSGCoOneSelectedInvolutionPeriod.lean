import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co1
import SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Tactic.FinCases

/-! A selected point-period certificate for the first pinned Co1 generator.
The actual vector returns after two steps and is moved after one. Genuine
unit generators bind this certificate to the literal model, proving even
order without a whole-matrix square, inverse or group-order certificate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoOneSelectedInvolutionPeriod

abbrev Model := CFSG.Models.MatrixGroups.Co1.Model
abbrev V := Fin 24 → ZMod 2

def firstMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  CFSG.Models.MatrixData.matrix 2 24 CFSG.Models.MatrixGroups.Co1.rows1

def initial : V := Pi.single (0 : Fin 24) 1

def firstEnd : Module.End (ZMod 2) V := Matrix.mulVecLin firstMatrix

/-- Selected finite obligation: no whole-operator identity is asserted. -/
theorem vector_return_two : (firstEnd ^ 2) initial = initial := by
  change firstMatrix *ᵥ (firstMatrix *ᵥ initial) = initial
  funext j
  fin_cases j <;> decide +kernel

/-- The selected vector is moved, witnessed at coordinate0 only. -/
theorem vector_nonreturn_one : firstEnd initial ≠ initial := by
  have hne : (firstEnd initial) (0 : Fin 24) ≠ initial 0 := by
    decide +kernel
  intro h
  exact hne (congrFun h (0 : Fin 24))

def unitAction : Model →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (Subgroup.closure (CFSG.Models.MatrixData.generators 2 24
        CFSG.Models.MatrixGroups.Co1.rows1 CFSG.Models.MatrixGroups.Co1.rows2)).subtype)

def unitEnd : Model →* Module.End (ZMod 2) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp unitAction

theorem exists_two_dvd_orderOf (hn : ¬IsMulCommutative Model) :
    ∃ g : Model, 2 ∣ orderOf g := by
  obtain ⟨x,hx,y,hy,hxa,hyb,_⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators 2 24
      CFSG.Models.MatrixGroups.Co1.rows1 CFSG.Models.MatrixGroups.Co1.rows2 hn
  let g : Model := ⟨x,Subgroup.subset_closure hx⟩
  have hraw : unitEnd g = firstEnd := by
    apply LinearMap.ext
    intro v
    change (x : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = firstMatrix *ᵥ v
    rw [hxa]
    rfl
  letI : MulAction Model V := MulAction.compHom V unitAction
  have hpow (n : ℕ) : g ^ n • initial = (firstEnd ^ n) initial := by
    change unitEnd (g ^ n) initial = (firstEnd ^ n) initial
    rw [map_pow,hraw]
  have hreturn : g ^ 2 • initial = initial := (hpow 2).trans vector_return_two
  have hone : g • initial = firstEnd initial := by
    simpa only [pow_one] using hpow 1
  have hmoved : g • initial ≠ initial :=
    fun h => vector_nonreturn_one (hone.symm.trans h)
  have hd : MulAction.period g initial ∣ 2 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp hreturn
  have hne : MulAction.period g initial ≠ 1 := by
    intro h
    exact hmoved (MulAction.period_eq_one_iff.mp h)
  have he : MulAction.period g initial = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hne
  refine ⟨g,?_⟩
  simpa only [he] using MulAction.period_dvd_orderOf g initial

theorem even_card (hn : ¬IsMulCommutative Model) : Even (Nat.card Model) := by
  obtain ⟨g,hg⟩ := exists_two_dvd_orderOf hn
  exact even_iff_two_dvd.mpr (hg.trans (orderOf_dvd_natCard g))

end SymmetricSubgroupAsymptotics.CFSGCoOneSelectedInvolutionPeriod
