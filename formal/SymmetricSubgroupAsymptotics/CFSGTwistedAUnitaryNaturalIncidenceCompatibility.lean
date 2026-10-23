import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalPointCompatibility

/-! The exact original inner point action transports incidence by
the SAME invertible natural matrix. This supplies both directions of
the normalization step for arbitrary maximal singular planes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem unitaryPointAction_inner_incidence (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) (P : unitarySingularPoints q s)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2)) :
    (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g)) P).val ≤
      unitarySubspaceImage q (s + 3) g S ↔ P.val ≤ S := by
  rw [unitarySingularPointAction_inner]
  change P.val.map (unitaryNaturalLinearEquiv q (s + 3) g).toLinearMap ≤
    S.map (unitaryNaturalLinearEquiv q (s + 3) g).toLinearMap ↔ P.val ≤ S
  exact Submodule.map_le_map_iff_of_injective (unitaryNaturalLinearEquiv q (s + 3) g).injective _ _

private theorem permutationHom_mul_apply {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (g h : G) (x : X) : rho (g * h) x = rho g (rho h x) := by
  exact congrFun (congrArg (fun p : Equiv.Perm X => (p : X → X)) (rho.map_mul g h)) x

theorem unitarySingularPointAction_mul_apply (q : CFSG.PrimePower) (s : ℕ)
    (f h : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P : unitarySingularPoints q s) :
    unitarySingularPointActionHom q s (f * h) P =
      unitarySingularPointActionHom q s f (unitarySingularPointActionHom q s h P) :=
  permutationHom_mul_apply (unitarySingularPointActionHom q s) f h P

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
