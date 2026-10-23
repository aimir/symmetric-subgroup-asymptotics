import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherRootCovariance
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFieldRootWords
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalAutomorphism

/-! Exact all-six positive-root covariance for the literal ORIGINAL
Ree automorphism. Cubic exceptional action and actual field-tensor beta
combine to alpha on short directions and beta on long directions, with
the required minus signs on the 2/4 exchange. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalHigherRootCovariance
open CFSGGTwoPositiveDirections CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalHigherRootCovariance CFSGGTwoExceptionalPositiveDirections
open CFSGGTwoOriginalFieldRootWords CFSGGTwoOriginalExceptionalModel
open CFSGGTwoOriginalExceptionalRootCovariance
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalAutomorphism

private theorem exceptional_beta (m : ℕ) (i : Fin 2) (t : Field m) :
    exceptionalParameter (Field m) i ((alphaEquiv m).symm t)=
      if i=0 then alpha m t else beta m t := by
  change exceptionalParameter (Field m) i (beta m t)=_
  by_cases hi : i=0
  · simp only [exceptionalParameter,if_pos hi]
    exact (alpha_eq_beta_cube m t).symm
  · simp only [exceptionalParameter,if_neg hi]

theorem ree_positiveModel (m : ℕ) (j : Fin 6) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) j t)=
      positiveModel (Field m) (exchangedDirection j)
        (signedParameter (Field m) j (if rootNode j=0 then alpha m t else beta m t)) := by
  change exceptionalModelEquiv (Field m)
      (fieldModel (Field m) (alphaEquiv m).symm (positiveModel (Field m) j t))=_
  rw [fieldModel_positiveModel,exceptional_positiveModel,exceptional_beta]

theorem ree_positiveModel_0 (m : ℕ) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) 0 t)=positiveModel (Field m) 1 (alpha m t) :=
  ree_positiveModel m 0 t

theorem ree_positiveModel_1 (m : ℕ) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) 1 t)=positiveModel (Field m) 0 (beta m t) :=
  ree_positiveModel m 1 t

theorem ree_positiveModel_2 (m : ℕ) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) 2 t)=positiveModel (Field m) 4 (-alpha m t) :=
  ree_positiveModel m 2 t

theorem ree_positiveModel_3 (m : ℕ) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) 3 t)=positiveModel (Field m) 5 (alpha m t) :=
  ree_positiveModel m 3 t

theorem ree_positiveModel_4 (m : ℕ) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) 4 t)=positiveModel (Field m) 2 (-beta m t) :=
  ree_positiveModel m 4 t

theorem ree_positiveModel_5 (m : ℕ) (t : Field m) :
    reeAutomorphism m (positiveModel (Field m) 5 t)=positiveModel (Field m) 3 (beta m t) :=
  ree_positiveModel m 5 t

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalHigherRootCovariance
