import SymmetricSubgroupAsymptotics.CFSGFFourTwistedScalarCompatibility
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorus

/-! The actual fixed torus has alpha-paired simple scalars. The unit
endomorphism is induced by the literal defining-field alpha map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarCompatibility
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom
open CFSGFFourTwistedScalarCompatibility

def alphaUnits (m : ℕ) : (Field m)ˣ →* (Field m)ˣ := Units.map (alpha m).toMonoidHom

theorem alphaUnits_val (m : ℕ) (a : (Field m)ˣ) :
    (alphaUnits m a : Field m)=alpha m (a : Field m) := rfl

theorem alphaUnits_twice (m : ℕ) (a : (Field m)ˣ) :
    alphaUnits m (alphaUnits m a)=a^2 := by
  apply Units.ext
  change alpha m (alpha m (a : Field m))=(a : Field m)^2
  exact alpha_twice m a

theorem fixed_middle_scalar_twist (m : ℕ) (a b : (Field m)ˣ) :
    powerHom relativeCartan (fixedTorusTuple m a b) 2=
      alphaUnits m (powerHom relativeCartan (fixedTorusTuple m a b) 1) := by
  change powerHom relativeCartan ![a,b,alphaUnits m b,alphaUnits m a] 2=
    alphaUnits m (powerHom relativeCartan ![a,b,alphaUnits m b,alphaUnits m a] 1)
  exact middle_scalar_twist (alphaUnits m) (alphaUnits_twice m) a b

theorem fixed_outer_scalar_twist (m : ℕ) (a b : (Field m)ˣ) :
    powerHom relativeCartan (fixedTorusTuple m a b) 3=
      alphaUnits m (powerHom relativeCartan (fixedTorusTuple m a b) 0) := by
  simp only [powerHom_apply,Fin.prod_univ_four]
  change a^(0:ℤ)*b^(0:ℤ)*(alphaUnits m b)^(-1:ℤ)*(alphaUnits m a)^(2:ℤ)=
    alphaUnits m (a^(2:ℤ)*b^(-1:ℤ)*(alphaUnits m b)^(0:ℤ)*(alphaUnits m a)^(0:ℤ))
  simp only [map_mul,map_inv,map_pow,zpow_zero,zpow_neg,zpow_ofNat,
    pow_zero,pow_one,map_one,one_mul,mul_one]
  ac_rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarCompatibility
