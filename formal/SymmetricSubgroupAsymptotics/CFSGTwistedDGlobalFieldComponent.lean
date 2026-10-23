import SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSingularDimension
import SymmetricSubgroupAsymptotics.CFSGTwistedDPointAction
import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalFieldCoherence

/-! One actual fixed-field automorphism works on all maximal singular
spaces for every actual projective automorphism. Local projective
semilinearity is proved from the original point/plane incidence, and
field coherence follows from the genuine nonsplit maximal gallery. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDGlobalFieldComponent
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDPointAction CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDMaximalSingularDimension CFSGTwistedA2FixedField
open CFSGQuadraticMaximalSingularGallery CFSGQuadraticMaximalFieldCoherence
open CFSGOrthogonalDIndexQuadraticSubspacePoints

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem exists_global_field_component (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) :
    ∃ sigma : fixedField q ≃+* fixedField q,
      ∀ M : MaximalSpaces (fixedQuadraticForm (s + 2) q),
        Nonempty (SemilinearPiece (fixedQuadraticForm (s + 2) q) (projectivePointActionHom s q f)
          ⟨M.val, M.property.1⟩ sigma) := by
  let A := fixedQuadraticForm (s + 2) q
  let pf := projectivePointActionHom s q f
  have hlocal : ∀ M : MaximalSpaces A, ∃ sigma : fixedField q ≃+* fixedField q,
      Nonempty (SemilinearPiece A pf ⟨M.val, M.property.1⟩ sigma) := by
    intro M
    apply exists_semilinearPiece A pf (singularActionHom s q f) (projectivePointAction_incidence s q f)
      ⟨M.val, M.property.1⟩ s
    exact maximalSingular_finrank (s + 2) q M.val M.property
  choose sigma hpiece using hlocal
  let F := fun M : MaximalSpaces A => Classical.choice (hpiece M)
  let B : MaximalSpaces A := ⟨positiveSpace (s + 2) q, positiveSpace_maximal (s + 2) q⟩
  refine ⟨sigma B, ?_⟩
  intro M
  have he : sigma M = sigma B := maximal_field_component_unique A pf
    (fun T => by rw [maximalSingular_finrank (s + 2) q T.val T.property]; omega)
    sigma F M B
  rw [← he]
  exact hpiece M

end SymmetricSubgroupAsymptotics.CFSGTwistedDGlobalFieldComponent
