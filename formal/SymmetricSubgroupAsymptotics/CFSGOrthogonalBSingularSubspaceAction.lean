import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointAction
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceAction

/-! The actual original B automorphism action extends to ALL original
singular subspaces, with reversible original point incidence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGIncidenceStarReconstruction
open CFSGPolarSubspacePoints
variable {K : Type} [Field K] [Finite K]

def originalPointPermutationHom (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    MulAut (elementaryProjective K (s+3)) →* Equiv.Perm (SingularPoints (K:=K) s) :=
  (relationAut (PointOrthogonal (K:=K) s)).subtype.comp (originalPointAction p h2 s)

def singularSubspaceAction (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    MulAut (elementaryProjective K (s+3)) →*
      Equiv.Perm (Subspaces (gram K (s+3)).toBilin') :=
  subspaceAction (gram K (s+3)).toBilin' (originalPointPermutationHom p h2 s)
    (singularActionHom p h2 s) (originalPointAction_incidence p h2 s)
    (originalPointAction_preserves_orthogonal p h2 s)

theorem singularSubspaceAction_incidence (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s+3)))
    (W : Subspaces (gram K (s+3)).toBilin') (P : SingularPoints (K:=K) s) :
    ((originalPointAction p h2 s f).val P).val ≤ (singularSubspaceAction p h2 s f W).val ↔
      P.val ≤ W.val :=
  subspaceAction_incidence (gram K (s+3)).toBilin' (originalPointPermutationHom p h2 s)
    (singularActionHom p h2 s) (originalPointAction_incidence p h2 s)
    (originalPointAction_preserves_orthogonal p h2 s) f W P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
