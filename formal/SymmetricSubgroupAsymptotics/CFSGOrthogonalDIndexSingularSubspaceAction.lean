import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarPointAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceCardinality

/-! The ACTUAL original projective D automorphism action on ALL
original Q-singular subspaces in ranks>=5, preserving incidence,
inclusion and dimension. No polar-only replacement in characteristic
two and no semilinear/triality assumption is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGIncidenceStarReconstruction CFSGOrthogonalDIndexQuadraticSubspacePoints
variable (K : Type) [Field K] [Finite K]

def originalPointPermutationHom (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) :
    MulAut (elementaryProjective K (s + 5)) →* Equiv.Perm (SingularPoints K s) :=
  (relationAut (PointOrthogonal K s)).subtype.comp (originalPointAction K p s)

def singularSubspaceAction (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) :
    MulAut (elementaryProjective K (s + 5)) →*
      Equiv.Perm (Subspaces (splitQuadraticForm K (s + 5))) :=
  subspaceAction (splitQuadraticForm K (s + 5)) (originalPointPermutationHom K p s)
    (singularActionHom K p (s + 1)) (originalPointAction_incidence K p s)

theorem singularSubspaceAction_incidence (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 5)))
    (W : Subspaces (splitQuadraticForm K (s + 5))) (P : SingularPoints K s) :
    ((originalPointAction K p s f).val P).val ≤ (singularSubspaceAction K p s f W).val ↔
      P.val ≤ W.val :=
  subspaceAction_incidence (splitQuadraticForm K (s + 5)) (originalPointPermutationHom K p s)
    (singularActionHom K p (s + 1)) (originalPointAction_incidence K p s) f W P

theorem singularSubspaceAction_preserves_le (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 5)))
    (W Z : Subspaces (splitQuadraticForm K (s + 5))) :
    (singularSubspaceAction K p s f W).val ≤ (singularSubspaceAction K p s f Z).val ↔
      W.val ≤ Z.val :=
  subspaceAction_preserves_le (splitQuadraticForm K (s + 5)) (originalPointPermutationHom K p s)
    (singularActionHom K p (s + 1)) (originalPointAction_incidence K p s) f W Z

theorem singularSubspaceAction_finrank (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 5)))
    (W : Subspaces (splitQuadraticForm K (s + 5))) :
    Module.finrank K (singularSubspaceAction K p s f W).val = Module.finrank K W.val :=
  imageSubspace_finrank (splitQuadraticForm K (s + 5)) (originalPointPermutationHom K p s f)
    (singularActionHom K p (s + 1) f) (originalPointAction_incidence K p s f) W

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
