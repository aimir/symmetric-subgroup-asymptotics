import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup

/-! The two literal fixed root parts generate J and are defining-prime
p-groups. This uses the checked original grading for both signs; no
order formula or Sylow property is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
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
  let R := rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K neg
  let f : rootPart K sigma neg →* R :=
    { toFun := fun x => ⟨x.val.val,x.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : R => z.val) he
  exact (rootGroup_isPGroup CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    E6Index K p neg).of_injective f hf

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootGeneratedPGroup
