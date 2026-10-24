import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentFieldActions
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveField

/-! Both literal positive simple blocks have the same full field action
after an original inner adjustment. Middle first-layer faithfulness is
proved on its actual torus normalizer, not assumed for the original Ree
automorphism. Signed recovery and the outer-order count remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveActions
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalOuterSemilinear CFSGReeFFourOriginalMiddleSemilinear
open CFSGReeFFourOriginalPositiveNormalization CFSGReeFFourOriginalCommonPositiveField

theorem middleAction_eq_fieldAut (m : ℕ) (hm : 0 < m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau) :
    middleAction m hm f = CFSGSuzukiUnipotentFieldActions.fieldAut m tau :=
  CFSGSuzukiUnipotentFieldActions.eq_fieldAut_of_first m hm (middleAction m hm f)
    (middleRestriction_mem_torus_normalizer m hm f) tau hfields.2

theorem middleAction_coordinate (m : ℕ) (hm : 0 < m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (a b : Field m) :
    middleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m a b) =
      CFSGSuzukiUnipotent.coordinateElement m (tau a) (tau b) := by
  rw [middleAction_eq_fieldAut m hm f tau hfields,
    CFSGSuzukiUnipotentFieldActions.fieldAut_coordinate]

theorem exists_inner_normalized_common_positive_actions (m : ℕ) (hm : 0 < m)
    (f : pairStabilizer m hm) :
    ∃ (z : CFSG.Models.ReeF4 m) (g : pairStabilizer m hm) (tau : Field m ≃+* Field m),
      innerAdjusted m hm f g z ∧ outerAction m hm g = tau.toAddEquiv ∧
        middleAction m hm g = CFSGSuzukiUnipotentFieldActions.fieldAut m tau := by
  obtain ⟨z,g,tau,hinner,hfields⟩ := exists_inner_normalized_common_positive_field m hm f
  refine ⟨z,g,tau,hinner,?_,middleAction_eq_fieldAut m hm g tau hfields⟩
  apply AddEquiv.ext
  intro x
  exact hfields.1 x

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveActions
