import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveField

/-! The normalized common positive field determines the action on the
literal original torus.  The two genuine scalar coordinates are
injective, and field automorphisms commute with the defining Frobenius
powers.  No ambient automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonDiagonalAction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourPerfectProjection CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalPositiveNormalization CFSGReeFFourOriginalDiagonalFieldAction
open CFSGReeFFourTorusScalarCoordinates CFSGReeFFourFixedTorusScalarCompatibility
open SemilinearScalarPairRigidity

theorem alphaUnits_field_map (m : ℕ) (tau : Field m ≃+* Field m) (b : (Field m)ˣ) :
    alphaUnits m (Units.map tau.toMonoidHom b) =
      Units.map tau.toMonoidHom (alphaUnits m b) := by
  apply Units.ext
  change alpha m (tau (b : Field m)) = tau (alpha m (b : Field m))
  simp only [alpha_apply, map_pow]

theorem scalarPair_field_map (m : ℕ) (tau : Field m ≃+* Field m)
    (a b : (Field m)ˣ) :
    scalarPair m (Units.map tau.toMonoidHom a, Units.map tau.toMonoidHom b) =
      diagonalAction tau tau (scalarPair m (a,b)) := by
  apply Prod.ext
  · change CFSGReeFFourFixedOuterTorusAction.outerScalar m
        (Units.map tau.toMonoidHom a) (Units.map tau.toMonoidHom b) =
      Units.map tau.toMonoidHom (CFSGReeFFourFixedOuterTorusAction.outerScalar m a b)
    simp only [outer_scalar_formula, map_mul, map_pow, map_inv]
  · change CFSGReeFFourFixedMiddleTorusAction.middleScalar m
        (Units.map tau.toMonoidHom a) (Units.map tau.toMonoidHom b) =
      Units.map tau.toMonoidHom (CFSGReeFFourFixedMiddleTorusAction.middleScalar m a b)
    simp only [middle_scalar_formula, map_mul, map_pow, map_inv, alphaUnits_field_map]

theorem original_torus_field_action (m : ℕ) (hm : 0 < m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (a b : (Field m)ˣ) :
    f.val (fixedToOriginal m hm (fixedTorus m a b)) =
      fixedToOriginal m hm (fixedTorus m (Units.map tau.toMonoidHom a)
        (Units.map tau.toMonoidHom b)) := by
  obtain ⟨c,d,himage,hscalar⟩ := exists_torus_image_scalarPair m hm f tau tau hfields a b
  have hparams : (c,d) = (Units.map tau.toMonoidHom a, Units.map tau.toMonoidHom b) :=
    scalarPair_injective m (hscalar.trans (scalarPair_field_map m tau a b).symm)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hparams
  exact himage

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonDiagonalAction
