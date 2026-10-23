import SymmetricSubgroupAsymptotics.CFSGDiagramMonomialSubgroup
import SymmetricSubgroupAsymptotics.CFSGCartanE6PowerIndex
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams
import Mathlib.Algebra.Group.Units.Equiv

/-! Compatible E6 relative root scalings are literal field-diagram fixed
six-tuples. The Cartan map restricts to them with image index at most
three. This is valid for every involution and every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeScalarTuples
open CFSGDiagramMonomialSubgroup CFSGSerreDiagram
open CFSGE6GeckFixedSimpleParameters

variable (K : Type) [Field K] (sigma : RingAut K)

def scalarTwist : MulAut Kˣ := Units.mapEquiv sigma.toMulEquiv

@[simp] theorem scalarTwist_val (t : Kˣ) :
    (scalarTwist K sigma t : K)=sigma (t : K) := rfl

def relativeScalars : Subgroup (Fin 6 → Kˣ) :=
  diagramTuples e6Permutation (scalarTwist K sigma)

def relativePowerHom : relativeScalars K sigma →* relativeScalars K sigma :=
  fixedPowerHom e6Permutation (scalarTwist K sigma) CartanMatrix.E₆ e6_preserves

@[simp] theorem relativePowerHom_val (x : relativeScalars K sigma) :
    (relativePowerHom K sigma x).val=CFSGIntegerMatrixPowerHom.powerHom CartanMatrix.E₆ x.val := rfl

theorem relativePowerHom_range_index_le [Finite K] :
    (relativePowerHom K sigma).range.index≤3 :=
  fixedPowerHom_range_index_le e6Permutation CartanMatrix.E₆ e6_preserves K
    (scalarTwist K sigma) CFSGCartanE6PowerIndex.certificate

def fixedUnit (t : (fixedCoefficient K sigma)ˣ) : Kˣ :=
  (Units.map (fixedCoefficient K sigma).subtype.toMonoidHom) t

theorem fixedUnit_twist (t : (fixedCoefficient K sigma)ˣ) :
    scalarTwist K sigma (fixedUnit K sigma t)=fixedUnit K sigma t := by
  apply Units.ext
  exact t.val.property

theorem scalarTwist_involutive (hsigma : Function.Involutive sigma) :
    Function.Involutive (scalarTwist K sigma) := by
  intro t
  apply Units.ext
  exact hsigma (t : K)

variable (hsigma : Function.Involutive sigma)

/-- Paired coordinates occupy nodes 0,2 and their partners 5,4;
singleton coordinates occupy nodes 3,1. -/
def scalarTuple (c d : Kˣ) (e h : (fixedCoefficient K sigma)ˣ) :
    relativeScalars K sigma :=
  ⟨![c,fixedUnit K sigma h,d,fixedUnit K sigma e,
      scalarTwist K sigma d,scalarTwist K sigma c],by
    change ∀ i,scalarTwist K sigma
      (![c,fixedUnit K sigma h,d,fixedUnit K sigma e,
        scalarTwist K sigma d,scalarTwist K sigma c] i)=
      ![c,fixedUnit K sigma h,d,fixedUnit K sigma e,
        scalarTwist K sigma d,scalarTwist K sigma c] (e6Permutation i)
    intro i
    fin_cases i
    · rfl
    · exact fixedUnit_twist K sigma h
    · rfl
    · exact fixedUnit_twist K sigma e
    · exact scalarTwist_involutive K sigma hsigma d
    · exact scalarTwist_involutive K sigma hsigma c⟩

@[simp] theorem scalarTuple_zero (c d : Kˣ) (e h : (fixedCoefficient K sigma)ˣ) :
    (scalarTuple K sigma hsigma c d e h).val 0=c := rfl

@[simp] theorem scalarTuple_two (c d : Kˣ) (e h : (fixedCoefficient K sigma)ˣ) :
    (scalarTuple K sigma hsigma c d e h).val 2=d := rfl

@[simp] theorem scalarTuple_three (c d : Kˣ) (e h : (fixedCoefficient K sigma)ˣ) :
    (scalarTuple K sigma hsigma c d e h).val 3=fixedUnit K sigma e := rfl

@[simp] theorem scalarTuple_one (c d : Kˣ) (e h : (fixedCoefficient K sigma)ˣ) :
    (scalarTuple K sigma hsigma c d e h).val 1=fixedUnit K sigma h := rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeScalarTuples
