import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterTorusCovariance
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalTorusScalarFaithful

/-! The two actual normalized positive fields coincide. The coupling
comes from the proved original outer Weyl coset and its genuine torus
reflection, rather than an assumed mixed-root or rank-one formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveField
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalPositiveNormalization CFSGReeFFourOriginalDiagonalFieldAction
open CFSGReeFFourOriginalOuterTorusCovariance CFSGReeFFourOriginalTorusScalarFaithful
open CFSGReeFFourTorusScalarCoordinates CFSGReeFFourFixedTorusScalarSurjectivity
open CFSGReeFFourFixedTorus CFSGReeFFourPerfectProjection
open SemilinearScalarPairRigidity
open CFSGReeFFourOriginalOuterWeylCoset

private theorem conjugate_eq {G : Type*} [Group G] (w : G) {x y : G}
    (he : x=y) : w*x*w⁻¹=w*y*w⁻¹ := congrArg (fun z=>w*z*w⁻¹) he

theorem normalized_positive_fields_eq (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau nu : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau nu) : tau=nu := by
  apply ringEquiv_eq_of_commute
  intro p
  obtain ⟨⟨a,b⟩,hab⟩ := scalar_pair_surjective m p
  obtain ⟨c,d,hF,hcd⟩ := exists_torus_image_scalarPair m hm f tau nu hfields a b
  obtain ⟨e,l,hFR,hel⟩ := exists_torus_image_scalarPair m hm f tau nu hfields (b*a⁻¹) b
  have hc := pair_outer_torus_covariance m hm f a b
  have hc' := hc.trans ((conjugate_eq (originalOuterWeyl m hm) hF).trans
    (original_outer_torus_reflection m hm c d))
  have hprojection : fixedToOriginal m hm (fixedTorus m e l)=
      fixedToOriginal m hm (fixedTorus m (d*c⁻¹) d) := hFR.symm.trans hc'
  have hcoords := scalarPair_eq_of_original_torus_eq m hm e l (d*c⁻¹) d hprojection
  have hp : scalarPair m (a,b)=p := hab
  have hcd' : scalarPair m (c,d)=diagonalAction tau nu p :=
    hcd.trans (congrArg (diagonalAction tau nu) hp)
  have hel' : scalarPair m (e,l)=diagonalAction tau nu (shearReflection p) :=
    hel.trans (congrArg (diagonalAction tau nu)
      ((scalarPair_outer_reflection m a b).trans (congrArg shearReflection hp)))
  exact hel'.symm.trans (hcoords.trans
    ((scalarPair_outer_reflection m c d).trans (congrArg shearReflection hcd')))

theorem exists_inner_normalized_common_positive_field (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃ (z : CFSG.Models.ReeF4 m) (g : pairStabilizer m hm) (tau : Field m ≃+* Field m),
      innerAdjusted m hm f g z ∧ positiveLayerDescription m hm g tau tau := by
  obtain ⟨z,g,tau,nu,hinner,hfields⟩ := exists_inner_normalized_positive_layers m hm f
  have he := normalized_positive_fields_eq m hm g tau nu hfields
  subst nu
  exact ⟨z,g,tau,hinner,hfields⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveField
