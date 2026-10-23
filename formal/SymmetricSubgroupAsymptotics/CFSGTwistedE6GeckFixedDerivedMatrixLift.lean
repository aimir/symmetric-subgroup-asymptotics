import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedLiftMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSylow

/-! Every ORIGINAL derived fixed action has a genuine fixed matrix lift.
The checked central-kernel cocycle theorem supplies this lift; the matrix
source representation is not assumed faithful or surjective on all fixes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedDerivedMatrixLift
open CFSGTwistedE6GeckDerivedLiftMembership CFSGTwistedE6GeckFixedPositiveSylow
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6FixedA2

def fixedMatrixAction (q : CFSG.PrimePower) :
    MatrixFixed q→*(Image (q.Extension 2)≃ₗ[q.Extension 2]Image (q.Extension 2)) :=
  (matrixAction (q.Extension 2)).comp (MatrixFixed q).subtype

theorem fixedMatrixAction_val (q : CFSG.PrimePower) (g : MatrixFixed q) :
    fixedMatrixAction q g=matrixAction (q.Extension 2) g.val := rfl

theorem exists_fixed_matrix_lift (q : CFSG.PrimePower) (d : Derived q) :
    ∃g : MatrixFixed q,fixedMatrixAction q g=derivedImageAction q d := by
  obtain ⟨v,_,hv,he⟩ := exists_original_derived_lift_in_commutator q d
  exact ⟨⟨v.val,hv⟩,he⟩

theorem derived_action_range_le_fixed_matrix_action (q : CFSG.PrimePower) :
    (derivedImageAction q).range≤(fixedMatrixAction q).range := by
  rintro y ⟨d,rfl⟩
  exact exists_fixed_matrix_lift q d

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedDerivedMatrixLift
