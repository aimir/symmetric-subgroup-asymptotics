import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPlaneNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarNormalizedCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPointSemilinearity

/-! Actual semilinear representatives on EVERY maximal singular plane
in natural dimensions4/5. Source and target normalization are literal
original-group words, and their inverse coordinate changes are retained
in the resulting semilinear map. No global field gluing is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGHermitianOrthogonalSpan CFSGTwistedAUnitaryNaturalRadical

private theorem cancel_linear_image_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (S : Submodule K V) (v : V)
    (h : S.map e.toLinearMap = K ∙ v) : S = K ∙ e.symm v := by
  have he := congrArg (fun T : Submodule K V => T.map e.symm.toLinearMap) h
  dsimp only at he
  rw [← Submodule.map_comp] at he
  have hi : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  rw [hi, Submodule.map_id, Submodule.map_span, Set.image_singleton] at he
  exact he

theorem exists_unitary_maximal_plane_semilinear (q : CFSG.PrimePower) (s : ℕ) (hs : s ≤ 1)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (S : {S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
      MaximalIsotropic (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) S}) :
    ∃ theta : q.Extension 2 ≃+* q.Extension 2,
      Function.Commute (definingFieldAutomorphism q 2) theta ∧
      ∃ M : S.val →ₛₗ[theta.toRingHom] (Fin (s + 4) → q.Extension 2),
        Function.Injective M ∧ ∀ (x : S.val) (hx : x ≠ 0) (P : unitarySingularPoints q s),
          P.val = (q.Extension 2) ∙ x.val →
          (unitarySingularPointActionHom q s f P).val = (q.Extension 2) ∙ M x := by
  obtain ⟨g, h, hg, hh, hinc⟩ := exists_unitaryStar_plane_normalization q s hs f S
  let F := unitaryStarTransportAut q s f g h
  obtain ⟨t, ht, htc0⟩ := exists_nonzero_central_parameter q (s + 1)
  have htc : t ∈ centralParameters q (s + 1) := (centralCondition_iff q (s + 1) t).mp htc0
  obtain ⟨theta, htheta, L, hL, hR⟩ := exists_unitaryStar_point_semilinear q s t ht htc F hinc
  let C := unitaryNormalizedPlaneCoordinates q s S.val g hg
  let A := unitaryNaturalLinearEquiv q (s + 3) h
  let M : S.val →ₛₗ[theta.toRingHom] (Fin (s + 4) → q.Extension 2) :=
    A.symm.toLinearMap.comp ((starVectorLinear q s).comp (L.comp C.toLinearMap))
  have hM : Function.Injective M := A.symm.injective.comp
    ((starVector_injective q s).comp (hL.comp C.injective))
  refine ⟨theta, htheta, M, hM, ?_⟩
  intro x hx P hP
  let v := C x
  have hv : v ≠ 0 := by
    intro hz
    apply hx
    apply C.injective
    exact hz.trans (map_zero C).symm
  have hG : unitarySingularPointActionHom q s
      (MulAut.conj (unitaryProjectiveCover q s g)) P = starPoint q s v hv := by
    apply Subtype.ext
    rw [unitarySingularPointAction_inner, hP, Submodule.map_span, Set.image_singleton]
    change (q.Extension 2) ∙ unitaryNaturalLinearEquiv q (s + 3) g x.val =
      (q.Extension 2) ∙ starVector q s v
    exact congrArg (fun z : Fin (s + 4) → q.Extension 2 => (q.Extension 2) ∙ z)
      (unitaryNormalizedPlaneCoordinates_reconstruct q s S.val g hg x).symm
  have hrel : unitarySingularPointActionHom q s F
      (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g)) P) =
      unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s h))
        (unitarySingularPointActionHom q s f P) := by
    simpa only [Equiv.symm_apply_apply] using unitaryStarTransportAut_point q s f g h
      (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s g)) P)
  have hrel' : unitarySingularPointActionHom q s F (starPoint q s v hv) =
      unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s h))
        (unitarySingularPointActionHom q s f P) :=
    (congrArg (unitarySingularPointActionHom q s F) hG).symm.trans hrel
  have hstar : (unitarySingularPointActionHom q s (MulAut.conj (unitaryProjectiveCover q s h))
      (unitarySingularPointActionHom q s f P)).val = (q.Extension 2) ∙ starVector q s (L v) :=
    (congrArg (fun Q : unitarySingularPoints q s => Q.val) hrel').symm.trans (hR v hv)
  have hmapped : (unitarySingularPointActionHom q s f P).val.map A.toLinearMap =
      (q.Extension 2) ∙ starVector q s (L v) := by
    exact (unitarySingularPointAction_inner q s h (unitarySingularPointActionHom q s f P)).symm.trans hstar
  exact cancel_linear_image_span A _ _ hmapped

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
