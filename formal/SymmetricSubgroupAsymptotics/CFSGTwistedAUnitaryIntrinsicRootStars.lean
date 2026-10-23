import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceAction

/-! Intrinsic root stars are joins of the ORIGINAL projective centre
root lines at the actual singular points of a subspace. Their covariance
under every original-model automorphism follows from the checked point
and maximal-subspace actions. No natural shear recognition is assumed
in these statements; the separate matrix installer proves that binding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices CFSGHermitianOrthogonalSpan

def unitaryPointRoot (q : CFSG.PrimePower) (s : ℕ) (P : unitarySingularPoints q s) :
    Subgroup (CFSG.Models.TwistedA (s + 3) q) :=
  unitaryCentralPointLabel q s ((unitaryCentralSingularPointEquiv q s).symm P)

theorem unitaryPointRoot_action (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P : unitarySingularPoints q s) :
    (unitaryPointRoot q s P).map f.toMonoidHom =
      unitaryPointRoot q s (unitarySingularPointActionHom q s f P) := by
  exact (unitaryCentralPointAction_label q s f
    ((unitaryCentralSingularPointEquiv q s).symm P)).symm

def unitaryRootStar (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2)) :
    Subgroup (CFSG.Models.TwistedA (s + 3) q) :=
  ⨆ P : {P : unitarySingularPoints q s // P.val ≤ S}, unitaryPointRoot q s P.val

theorem unitaryPointRoot_le_star (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (P : unitarySingularPoints q s) (hP : P.val ≤ S) :
    unitaryPointRoot q s P ≤ unitaryRootStar q s S :=
  le_iSup (fun Q : {Q : unitarySingularPoints q s // Q.val ≤ S} => unitaryPointRoot q s Q.val) ⟨P, hP⟩

theorem unitaryRootStar_map_of_incidence (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S T : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ T ↔ P.val ≤ S) :
    (unitaryRootStar q s S).map f.toMonoidHom = unitaryRootStar q s T := by
  apply le_antisymm
  · rw [unitaryRootStar, Subgroup.map_iSup]
    apply iSup_le
    intro P
    rw [unitaryPointRoot_action]
    exact unitaryPointRoot_le_star q s T _ ((hinc P.val).mpr P.property)
  · apply iSup_le
    intro Q
    let P := (unitarySingularPointActionHom q s f).symm Q.val
    have he : unitarySingularPointActionHom q s f P = Q.val :=
      (unitarySingularPointActionHom q s f).apply_symm_apply Q.val
    have hP : P.val ≤ S := (hinc P).mp (he.symm ▸ Q.property)
    calc
      unitaryPointRoot q s Q.val = unitaryPointRoot q s (unitarySingularPointActionHom q s f P) :=
        congrArg (unitaryPointRoot q s) he.symm
      _ = (unitaryPointRoot q s P).map f.toMonoidHom := (unitaryPointRoot_action q s f P).symm
      _ ≤ (unitaryRootStar q s S).map f.toMonoidHom :=
        Subgroup.map_mono (unitaryPointRoot_le_star q s S P hP)

theorem unitaryRootStar_maximal_action (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : {S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
      MaximalIsotropic (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S}) :
    (unitaryRootStar q s S.val).map f.toMonoidHom =
      unitaryRootStar q s (unitaryMaximalIsotropicActionHom q s f S).val :=
  unitaryRootStar_map_of_incidence q s f _ _
    (unitaryMaximalIsotropicAction_incidence q s f S)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
