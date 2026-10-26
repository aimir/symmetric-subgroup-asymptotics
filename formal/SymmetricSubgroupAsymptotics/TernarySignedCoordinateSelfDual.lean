import SymmetricSubgroupAsymptotics.SignedMonomialCoordinateSelfDual
import SymmetricSubgroupAsymptotics.TernaryFourProperModuleSignKernel
import SymmetricSubgroupAsymptotics.AbelianSemidirectDualClassIdentity
import SymmetricSubgroupAsymptotics.SignedMonomialStabilizerClassBound

/-! Literal binary signs are their own inverses. Consequently the
coordinate pairing identifies the primal and contragredient stabilizers
inside the SAME signed subgroup, with no splitting hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernarySignedCoordinateSelfDual
open TernarySignedWreathLinearEquiv SignedMonomialCoordinateSelfDual

local instance {I : Type} : Module (ZMod 3) (Additive (Multiplicative (I → ZMod 3))) :=
  inferInstanceAs (Module (ZMod 3) (I → ZMod 3))

theorem coefficient_inv (I : Type) (g : Model I) (i : I) :
    coefficient I g⁻¹ ((permutationHom I g).symm i)=coefficient I g i := by
  have hsign (s : Multiplicative (ZMod 2)) : s⁻¹=s := by
    apply Multiplicative.toAdd.injective
    exact ZMod.neg_eq_self_mod_two s.toAdd
  change OddMarkerTernaryChart.signUnitHom
      ((g.left (g.right (g.right.symm i)))⁻¹)=
    OddMarkerTernaryChart.signUnitHom (g.left i)
  rw [Equiv.apply_symm_apply,hsign]

theorem coordinateDualEquiv_intertwines_subgroup
    {I : Type} [Finite I] (R : Subgroup (Model I))
    (g : R) (v : I → ZMod 3) :
    coordinateDualEquiv (((linearHom I).comp R.subtype) g v)=
      LinearContragredientSmallSpaceAction.contragredient
        ((linearHom I).comp R.subtype) g (coordinateDualEquiv v) := by
  exact coordinateDualEquiv_intertwines
    ((linearHom I).comp R.subtype) ((permutationHom I).comp R.subtype)
    (fun g i => coefficient I g.val i)
    (fun g w i => linearHom_apply I g.val w i)
    (fun g i => coefficient_inv I g.val i) g v

theorem dualStabilizer_eq_fixedSubgroup
    {I : Type} [Finite I] (R : Subgroup (Model I)) (v : I → ZMod 3) :
    AbelianSemidirectDualClassIdentity.dualStabilizer
        (N:=Multiplicative (I → ZMod 3))
        ((linearHom I).comp R.subtype) (coordinateDualEquiv v)=
      SignedMonomialStabilizerClassBound.fixedSubgroup
        ((linearHom I).comp R.subtype) v := by
  ext g
  change LinearContragredientSmallSpaceAction.contragredient
      ((linearHom I).comp R.subtype) g (coordinateDualEquiv v)=coordinateDualEquiv v ↔
    ((linearHom I).comp R.subtype) g v=v
  rw [←coordinateDualEquiv_intertwines_subgroup R g v]
  exact (coordinateDualEquiv (I:=I) (K:=ZMod 3)).injective.eq_iff

end SymmetricSubgroupAsymptotics.TernarySignedCoordinateSelfDual
