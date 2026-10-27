import SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators
import Mathlib.GroupTheory.GroupAction.Period

/-! Generic bridge extracted from the checked selected Co1 pilot.
A return at2 and nonreturn at1 for one vector under the FIRST literal
matrix suffice for even cardinality of the SAME original matrix model.
Noncommutativity supplies genuine units in its two fibres. No raw matrix
invertibility, whole-matrix power, field primality, finiteness or simplicity
premise is assumed. The selected vector equations remain explicit inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.MatrixModelSelectedPointPeriodTwo

abbrev Model (p n : ℕ) (a b : Array String) := CFSG.Models.MatrixData.Model p n a b
abbrev Vector (p n : ℕ) := Fin n → ZMod p

def firstEnd (p n : ℕ) (a : Array String) : Module.End (ZMod p) (Vector p n) :=
  Matrix.mulVecLin (CFSG.Models.MatrixData.matrix p n a)

def unitAction (p n : ℕ) (a b : Array String) :
    Model p n a b →* (Vector p n ≃ₗ[ZMod p] Vector p n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Vector p n)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (Subgroup.closure (CFSG.Models.MatrixData.generators p n a b)).subtype)

def unitEnd (p n : ℕ) (a b : Array String) :
    Model p n a b →* Module.End (ZMod p) (Vector p n) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (unitAction p n a b)

theorem exists_two_dvd_orderOf (p n : ℕ) (a b : Array String) (v : Vector p n)
    (hreturn : (firstEnd p n a ^ 2) v = v)
    (hmoved : firstEnd p n a v ≠ v)
    (hn : ¬IsMulCommutative (Model p n a b)) :
    ∃ g : Model p n a b, 2 ∣ orderOf g := by
  obtain ⟨x,hx,y,hy,hxa,hyb,_⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let g : Model p n a b := ⟨x,Subgroup.subset_closure hx⟩
  have hraw : unitEnd p n a b g = firstEnd p n a := by
    apply LinearMap.ext
    intro w
    change (x : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ w = firstEnd p n a w
    rw [hxa]
    rfl
  letI : MulAction (Model p n a b) (Vector p n) :=
    MulAction.compHom (Vector p n) (unitAction p n a b)
  have hpow (k : ℕ) : g ^ k • v = (firstEnd p n a ^ k) v := by
    change unitEnd p n a b (g ^ k) v = (firstEnd p n a ^ k) v
    rw [map_pow,hraw]
  have htwo : g ^ 2 • v = v := (hpow 2).trans hreturn
  have hone : g • v = firstEnd p n a v := by
    simpa only [pow_one] using hpow 1
  have hne : g • v ≠ v := fun h => hmoved (hone.symm.trans h)
  have hd : MulAction.period g v ∣ 2 :=
    MulAction.pow_smul_eq_iff_period_dvd.mp htwo
  have hperiod : MulAction.period g v ≠ 1 := by
    intro h
    exact hne (MulAction.period_eq_one_iff.mp h)
  have he : MulAction.period g v = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hperiod
  exact ⟨g,by simpa only [he] using MulAction.period_dvd_orderOf g v⟩

theorem even_card_of_first_vector_period_two (p n : ℕ) (a b : Array String)
    (v : Vector p n) (hreturn : (firstEnd p n a ^ 2) v = v)
    (hmoved : firstEnd p n a v ≠ v)
    (hn : ¬IsMulCommutative (Model p n a b)) : Even (Nat.card (Model p n a b)) := by
  obtain ⟨g,hg⟩ := exists_two_dvd_orderOf p n a b v hreturn hmoved hn
  exact even_iff_two_dvd.mpr (hg.trans (orderOf_dvd_natCard g))

end SymmetricSubgroupAsymptotics.MatrixModelSelectedPointPeriodTwo
