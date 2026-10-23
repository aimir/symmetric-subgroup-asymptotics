import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup

/-! The two literal fixed root parts generate J and are defining-prime
p-groups. This uses the checked original grading for both signs; no
order formula or Sylow property is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityD4NormTwo CFSGTrialityGeckRelativeRootGenerated
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositivePGroup

def rootPart (K : Type) [Field K] (sigma : K ≃+* K) (neg : Bool) :
    Subgroup (fixedRootGenerated K sigma) :=
  (signedFixed K sigma neg).subgroupOf (fixedRootGenerated K sigma)

theorem rootPart_sup (K : Type) [Field K] (sigma : K ≃+* K) :
    rootPart K sigma false ⊔ rootPart K sigma true = ⊤ := by
  rw [rootPart,rootPart,←Subgroup.subgroupOf_sup
    (signedFixed_le_generated K sigma false) (signedFixed_le_generated K sigma true)]
  exact Subgroup.subgroupOf_self _

theorem rootPart_isPGroup (K : Type) [Field K] (sigma : K ≃+* K)
    (p : ℕ) [Fact p.Prime] [CharP K p] (neg : Bool) : IsPGroup p (rootPart K sigma neg) := by
  let R := rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K neg
  let f : rootPart K sigma neg →* R :=
    { toFun := fun x => ⟨x.val.val,x.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : R => z.val) he
  exact (rootGroup_isPGroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    Index K p neg).of_injective f hf

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup
