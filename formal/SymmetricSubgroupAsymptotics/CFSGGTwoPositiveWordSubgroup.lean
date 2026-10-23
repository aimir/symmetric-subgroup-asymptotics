import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordMultiplication
import Mathlib.SetTheory.Cardinal.Finite

/-! The six-root word range is an actual subgroup in characteristic three,
with explicit inverses and exact cardinality. No ambient positive-subgroup
recognition or exceptional fixed-point theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordSubgroup
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords CFSGGTwoPositiveSixWord
open CFSGGTwoOriginalPositiveCollecting CFSGGTwoPositiveWordMultiplication
variable (K : Type) [Field K] [CharP K 3]

def inverseCoordinates (x : Fin 6 → K) : Fin 6 → K :=
  ![-x 0,-x 1,-x 2-x 0*x 1,-x 3-x 0*x 2+(x 0)^2*x 1,
    -x 4-(x 0)^3*x 1,-x 5+x 1*x 4+2*(x 0)^3*(x 1)^2]

theorem productCoordinates_inverse (x : Fin 6 → K) :
    productCoordinates K x (inverseCoordinates K x)=0 := by
  funext i
  fin_cases i <;> simp [productCoordinates,inverseCoordinates] <;> ring

theorem modelWord_zero : modelWord K 0=1 := by
  simp only [modelWord,Pi.zero_apply,positiveModel_zero,one_mul]

theorem modelWord_inverse (x : Fin 6 → K) :
    modelWord K (inverseCoordinates K x)=(modelWord K x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [modelWord_mul,productCoordinates_inverse,modelWord_zero]

/-- Literal six-word range, with closure established by the actual collected
product formula and the explicit inverse above. -/
def positiveWordGroup : Subgroup (Model CartanMatrix.G₂ K) where
  carrier := Set.range (modelWord K)
  one_mem' := ⟨0,modelWord_zero K⟩
  mul_mem' := by
    rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
    exact ⟨productCoordinates K x y,(modelWord_mul K x y).symm⟩
  inv_mem' := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inverseCoordinates K x,modelWord_inverse K x⟩

theorem mem_positiveWordGroup (g : Model CartanMatrix.G₂ K) :
    g∈positiveWordGroup K ↔ ∃ x,modelWord K x=g := Iff.rfl

def positiveWordEquiv : (Fin 6 → K) ≃ positiveWordGroup K :=
  Equiv.ofInjective (modelWord K) (modelWord_injective K)

theorem positiveWordGroup_card : Nat.card (positiveWordGroup K)=(Nat.card K)^6 := by
  rw [←Nat.card_congr (positiveWordEquiv K),Nat.card_fun,Nat.card_fin]

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordSubgroup
