import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRangePreimage

/-! A named positive Sylow in J(K,sigma), for an arbitrary finite field
and field automorphism. It is the actual intersection with the checked
ambient fixed Sylow, and its carrier is exactly the literal rootPart.
No source action or representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedSylow
open CFSGTrialityGeckFixedPositiveSylow CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckFixedRangePreimage
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
variable (K : Type) [Field K] [Finite K] (sigma : K≃+*K)

def generatedToFixed : fixedRootGenerated K sigma→*MatrixFixed K sigma where
  toFun g := ⟨⟨g.val,fixedRootGenerated_le_matrixGroup K sigma g.property⟩,by
    apply Subtype.ext
    exact fixedRootGenerated_le_fixed K sigma g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem generatedToFixed_injective : Function.Injective (generatedToFixed K sigma) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : MatrixFixed K sigma=>z.val.val) he)

theorem fixed_positive_le_generated_range (p : ℕ) [Fact p.Prime] [CharP K p] :
    (fixedPositiveSylow K sigma p : Subgroup (MatrixFixed K sigma))≤(generatedToFixed K sigma).range := by
  intro x hx
  have hp : x.val.val∈Positive K := hx
  have hf := congrArg (fun z : MatrixGroup K=>z.val) x.property
  change unitTwist K sigma x.val.val=x.val.val at hf
  have hs : x.val.val∈signedFixed K sigma false := ⟨hp,hf⟩
  refine ⟨⟨x.val.val,signedFixed_le_generated K sigma false hs⟩,?_⟩
  exact Subtype.ext (Subtype.ext rfl)

def positiveSylow (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (fixedRootGenerated K sigma) :=
  (fixedPositiveSylow K sigma p).comapOfInjective (generatedToFixed K sigma)
    (generatedToFixed_injective K sigma) (fixed_positive_le_generated_range K sigma p)

theorem positiveSylow_coe (p : ℕ) [Fact p.Prime] [CharP K p] :
    (positiveSylow K sigma p : Subgroup (fixedRootGenerated K sigma))=rootPart K sigma false := by
  ext x
  constructor
  · intro hx
    have hp : x.val∈Positive K := hx
    exact ⟨hp,fixedRootGenerated_le_fixed K sigma x.property⟩
  · intro hx
    exact hx.1

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedSylow
