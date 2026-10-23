import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootGeneratedPGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRangePreimage

/-! A named actual Sylow of J is exactly its literal positive root part.
It is pulled back injectively from the checked matrix fixed subgroup;
no original source or action representation is assumed faithful. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckGeneratedPositiveSylow
open CFSGTwistedE6GeckFixedPositiveSylow CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist CFSGSerreOrdinaryTwists
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

def generatedToMatrixFixed (q : CFSG.PrimePower) :
    fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)→*MatrixFixed q where
  toFun g := ⟨⟨g.val,fixedRootGenerated_le_matrixGroup (q.Extension 2)
    (definingFieldAutomorphism q 2) g.property⟩,by
      apply Subtype.ext
      exact fixedRootGenerated_le_fixed (q.Extension 2) (definingFieldAutomorphism q 2) g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem generatedToMatrixFixed_injective (q : CFSG.PrimePower) :
    Function.Injective (generatedToMatrixFixed q) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : MatrixFixed q=>z.val.val) he)

theorem fixed_positive_le_generated_range (q : CFSG.PrimePower) :
    (fixedPositiveSylow q : Subgroup (MatrixFixed q))≤(generatedToMatrixFixed q).range := by
  intro x hx
  have hp : x.val.val∈Positive (q.Extension 2) := hx
  have hf := congrArg (fun z : MatrixGroup (q.Extension 2)=>z.val) x.property
  dsimp only at hf
  have hs : x.val.val∈signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false := ⟨hp,hf⟩
  refine ⟨⟨x.val.val,signedFixed_le_generated (q.Extension 2)
    (definingFieldAutomorphism q 2) false hs⟩,?_⟩
  exact Subtype.ext (Subtype.ext rfl)

def generatedPositiveSylow (q : CFSG.PrimePower) :
    Sylow q.prime (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) :=
  (fixedPositiveSylow q).comapOfInjective (generatedToMatrixFixed q)
    (generatedToMatrixFixed_injective q) (fixed_positive_le_generated_range q)

theorem generatedPositiveSylow_coe (q : CFSG.PrimePower) :
    (generatedPositiveSylow q : Subgroup (fixedRootGenerated (q.Extension 2)
      (definingFieldAutomorphism q 2)))=
      rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false := by
  ext x
  constructor
  · intro hx
    have hp : x.val∈Positive (q.Extension 2) := hx
    exact ⟨hp,fixedRootGenerated_le_fixed (q.Extension 2) (definingFieldAutomorphism q 2) x.property⟩
  · intro hx
    exact hx.1

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckGeneratedPositiveSylow
