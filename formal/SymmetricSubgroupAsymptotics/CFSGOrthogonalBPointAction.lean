import SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11CommonNeighbourCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointActionFromCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneActionFaithful

/-! The actual original projective B automorphism action on singular
points, with the R11 count proved internally. No point-recognition,
count, arbitrary automorphism-lifting, or semilinear premise is retained.
Faithfulness uses the exact simplicity property of the classified model;
the quantitative outer-automorphism bound is still a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGIncidenceStarReconstruction
variable {K : Type} [Field K] [Finite K]

def originalPointAction (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    MulAut (elementaryProjective K (s+3)) →* relationAut (PointOrthogonal (K:=K) s) :=
  originalPointActionOfCount p h2 s (r11_common_neighbours_large h2 s)

theorem originalPointAction_incidence (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s+3)))
    (U : SingularPoints (K:=K) s) (P : SingularPlanes (K:=K) s) :
    ((originalPointAction p h2 s f).val U).val≤(singularActionHom p h2 s f P).val ↔ U.val≤P.val :=
  originalPointActionOfCount_incidence p h2 s (r11_common_neighbours_large h2 s) f U P

theorem originalPointAction_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+3))] :
    Function.Injective (originalPointAction (K:=K) p h2 s) := by
  have hi : Function.Injective
      (planeRelationActionOfCount p h2 s (r11_common_neighbours_large h2 s)) := by
    intro f g h
    apply singularActionHom_injective p h2 s
    exact congrArg Subtype.val h
  exact (polarPointAction_injective h2 s).comp hi

theorem originalPointAction_preserves_orthogonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s+3)))
    (U V : SingularPoints (K:=K) s) :
    PointOrthogonal s ((originalPointAction p h2 s f).val U)
      ((originalPointAction p h2 s f).val V) ↔ PointOrthogonal s U V :=
  (originalPointAction p h2 s f).property U V

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
