import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalIncidenceCompatibility
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarStandardPlane
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMaximalSubspaceAction

/-! Any ORIGINAL automorphism and any literal maximal singular plane
in natural dimensions4/5 can be normalized to the canonical star
stabilizer using actual original inner words on source and target.
The stabilizer condition is proved from exact point incidence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGHermitianOrthogonalSpan

def unitaryStarTransportAut (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (g h : naturalFixed (s + 3) q) :
    MulAut (CFSG.Models.TwistedA (s + 3) q) :=
  MulAut.conj (unitaryProjectiveCover q s h) * f * (MulAut.conj (unitaryProjectiveCover q s g))⁻¹

private theorem permutationHom_inverse_apply {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (g : G) (x : X) : rho g⁻¹ x = (rho g).symm x := by
  rw [map_inv]
  rfl

private theorem permutationHom_normalized_apply {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (f g h : G) (x : X) :
    rho (h * f * g⁻¹) x = rho h (rho f ((rho g).symm x)) := by
  simp only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply, permutationHom_inverse_apply]

private theorem normalized_predicate {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (f g h : G) (A B C : X → Prop)
    (hg : ∀ x, A (rho g x) ↔ B x) (hh : ∀ x, A (rho h x) ↔ C x)
    (hf : ∀ x, C (rho f x) ↔ B x) :
    ∀ x, A (rho (h * f * g⁻¹) x) ↔ A x := by
  intro x
  rw [permutationHom_normalized_apply, hh, hf]
  have he := hg ((rho g).symm x)
  simpa only [Equiv.apply_symm_apply] using he.symm

private theorem incidence_target_eq {V : Type*} [LE V] (P S T : V) (h : S = T)
    (B : Prop) (hb : P ≤ S ↔ B) : P ≤ T ↔ B := by
  subst T
  exact hb

theorem unitaryStarTransportAut_point (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (g h : naturalFixed (s + 3) q)
    (P : unitarySingularPoints q s) :
    unitarySingularPointActionHom q s (unitaryStarTransportAut q s f g h) P =
      unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s h))
        (unitarySingularPointActionHom q s f
          ((unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g))).symm P)) := by
  exact permutationHom_normalized_apply (unitarySingularPointActionHom q s) f
    (MulAut.conj (unitaryProjectiveCover q s g)) (MulAut.conj (unitaryProjectiveCover q s h)) P

theorem exists_unitaryStar_plane_normalization (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : {S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
      MaximalIsotropic (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S}) :
    ∃ g h : naturalFixed (s + 3) q,
      unitarySubspaceImage q (s + 3) g S.val = starPlane q s ∧
      unitarySubspaceImage q (s + 3) h (unitaryMaximalIsotropicActionHom q s f S).val = starPlane q s ∧
      ∀ P : unitarySingularPoints q s,
        (unitarySingularPointActionHom q s (unitaryStarTransportAut q s f g h) P).val ≤ starPlane q s ↔
          P.val ≤ starPlane q s := by
  obtain ⟨g, hg⟩ := exists_normalize_maximal_to_starPlane q s hs S.val S.property
  obtain ⟨h, hh⟩ := exists_normalize_maximal_to_starPlane q s hs
    (unitaryMaximalIsotropicActionHom q s f S).val (unitaryMaximalIsotropicActionHom q s f S).property
  refine ⟨g, h, hg, hh, ?_⟩
  have hG (Q : unitarySingularPoints q s) :
      (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g)) Q).val ≤
        starPlane q s ↔ Q.val ≤ S.val := by
    exact incidence_target_eq _ _ _ hg _ (unitaryPointAction_inner_incidence q s g Q S.val)
  have hH (Q : unitarySingularPoints q s) :
      (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s h)) Q).val ≤
        starPlane q s ↔ Q.val ≤ (unitaryMaximalIsotropicActionHom q s f S).val := by
    exact incidence_target_eq _ _ _ hh _ (unitaryPointAction_inner_incidence q s h Q _)
  exact normalized_predicate (unitarySingularPointActionHom q s) f
    (MulAut.conj (unitaryProjectiveCover q s g)) (MulAut.conj (unitaryProjectiveCover q s h))
    (fun P => P.val ≤ starPlane q s) (fun P => P.val ≤ S.val)
    (fun P => P.val ≤ (unitaryMaximalIsotropicActionHom q s f S).val)
    hG hH (fun P => unitaryMaximalIsotropicAction_incidence q s f S P)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
