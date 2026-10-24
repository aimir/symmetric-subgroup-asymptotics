import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex

/-! The same explicit integral inverse also gives injectivity of the F4
relative scalar map over every commutative group. This retains actual
torus coordinates when imposing the exceptional fixed-point equations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarInjective
open CFSGIntegerMatrixPowerHom CFSGFFourRelativeScalarIndex

theorem relativeCartan_left_inverse : inverseExponents*relativeCartan=1 := by decide

theorem powerHom_injective {G : Type*} [CommGroup G] :
    Function.Injective (powerHom (G:=G) relativeCartan) := by
  have hinv : Function.LeftInverse (powerHom (G:=G) inverseExponents)
      (powerHom (G:=G) relativeCartan) :=
    powerHom_rightInverse inverseExponents relativeCartan relativeCartan_left_inverse
  exact hinv.injective

end SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarInjective
