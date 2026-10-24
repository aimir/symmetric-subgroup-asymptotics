import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorus
import SymmetricSubgroupAsymptotics.CFSGFFourOuterTorusScalars
import Mathlib.Algebra.CharP.Two

/-! The genuine fixed torus with second parameter one scales every
relative simple root nontrivially when its first parameter is not one.
No assertion is made here about derived membership or the Tits case. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalars
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourParameterizedTorusCovariance
open CFSGFFourOuterTorusScalars CFSGIntegerMatrixPowerHom CFSGFFourRelativeScalarIndex

theorem unitPower_one (m : ℕ) (i : Fin 4) : unitPower m i 1=1 := by
  apply Units.ext
  rw [unitPower_val]
  simp

theorem fixed_torus_scalars (m : ℕ) (a : (Field m)ˣ) :
    powerHom relativeCartan (fixedTorusTuple m a 1)=
      ![a^2,a⁻¹,(unitPower m 0 a)⁻¹,(unitPower m 0 a)^2] := by
  have ht : fixedTorusTuple m a 1=![a,1,1,unitPower m 0 a] := by
    funext i
    fin_cases i <;> simp [fixedTorusTuple,unitPower_one]
  rw [ht,outer_torus_scalars]

private theorem square_ne_one {K : Type*} [Field K] [CharP K 2]
    (a : Kˣ) (ha : a≠1) : ((a^2 : Kˣ) : K)≠1 := by
  intro he
  have hs : (a : K)^2=1 := by simpa only [Units.val_pow_eq_pow_val] using he
  have hn : ((a : K)-1)^2=0 := by
    rw [CharTwo.sub_eq_add,CharTwo.add_sq]
    rw [hs,one_pow,CharTwo.add_self_eq_zero]
  have hv : (a : K)=1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact ha (Units.ext hv)

theorem fixed_torus_scalars_ne_one (m : ℕ) (a : (Field m)ˣ) (ha : a≠1)
    (i : Fin 4) :
    ((powerHom relativeCartan (fixedTorusTuple m a 1) i : (Field m)ˣ) : Field m)≠1 := by
  have hu : unitPower m 0 a≠1 := by
    intro he
    apply ha
    have h := congrArg (unitPower m (CFSG.Models.reverseNode 0)) he
    simpa only [unitPower_reverse,unitPower_one] using h
  rw [fixed_torus_scalars]
  fin_cases i
  · exact square_ne_one a ha
  · change ((a⁻¹ : (Field m)ˣ) : Field m)≠1
    intro he
    exact ha (inv_eq_one.mp (show a⁻¹=1 from Units.ext he))
  · change (((unitPower m 0 a)⁻¹ : (Field m)ˣ) : Field m)≠1
    intro he
    exact hu (inv_eq_one.mp (show (unitPower m 0 a)⁻¹=1 from Units.ext he))
  · exact square_ne_one (unitPower m 0 a) hu

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalars
