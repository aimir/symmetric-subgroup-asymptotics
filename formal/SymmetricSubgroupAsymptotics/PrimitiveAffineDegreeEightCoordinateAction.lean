import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightLinearEmbedding
import SymmetricSubgroupAsymptotics.ElementaryZModAutomorphismCoordinates

/-! Actual degree-eight translation coordinates and the intertwined matrix
action of the actual point stabilizer. This strengthens the faithful matrix
embedding by keeping its action on the original regular subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]

private def withPrimeTwo (P : PrimitiveAffineProfile L Ω) (hp : P.p = 2) :
    PrimitiveAffineProfile L Ω where
  p := 2
  p_prime := by decide
  V := P.V
  V_normal := P.V_normal
  V_pgroup := by rw [← hp]; exact P.V_pgroup
  regular := P.regular

theorem translationCoordinates_degreeEight_nonempty
    [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
    (P : PrimitiveAffineProfile L Ω) (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (hdegree : Nat.card Ω = 8) :
    Nonempty (P.V ≃* Multiplicative (Fin 3 → ZMod 2)) := by
  have hp := (P.degreeEight_prime_dimension hprimitive x hdegree).1
  let Q := withPrimeTwo P hp
  let C := Q.elementaryChart hprimitive
  letI : Fact (Nat.Prime 2) := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod 2) C.V := C.module
  letI : FiniteDimensional (ZMod 2) C.V := C.finiteDimensional
  have hfin : Module.finrank (ZMod 2) C.V = 3 := by
    simpa only [ElementaryChart.d] using
      (Q.degreeEight_prime_dimension hprimitive x hdegree).2
  let basis : Module.Basis (Fin 3) (ZMod 2) C.V :=
    Module.finBasisOfFinrankEq (ZMod 2) C.V hfin
  exact ⟨C.equiv.trans basis.equivFun.toAddEquiv.toMultiplicative⟩

/-- Every supplied actual translation chart determines a faithful matrix
map of the actual point stabilizer, with no arbitrary representation choice. -/
def complementCoordinateMap (P : PrimitiveAffineProfile L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2)) :
    P.complement x →* StandardThreeDimensionalLinearGroups.GeneralThree 2 :=
  (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3).toMonoidHom.comp
    ((MulAut.congr a).toMonoidHom.comp (P.complementAction x))

theorem complementCoordinateMap_injective [FaithfulSMul L Ω]
    (P : PrimitiveAffineProfile L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2)) :
    Function.Injective (P.complementCoordinateMap x a) :=
  (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3).injective.comp
    ((MulAut.congr a).injective.comp (P.complementAction_injective x))

/-- The matrix action is exactly conjugation on the original translations
under the specified coordinates. -/
theorem complementCoordinateMap_action
    (P : PrimitiveAffineProfile L Ω) (x : Ω)
    (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2))
    (k : P.complement x) (v : P.V) :
    (P.complementCoordinateMap x a k).val *ᵥ (a v).toAdd =
      (a (P.complementAction x k v)).toAdd := by
  change (ElementaryZModAutomorphismCoordinates.matrixEquiv 2 3
    ((MulAut.congr a) (P.complementAction x k))).val *ᵥ (a v).toAdd = _
  rw [ElementaryZModAutomorphismCoordinates.matrixEquiv_apply]
  change (a (P.complementAction x k (a.symm (a v)))).toAdd = _
  rw [a.symm_apply_apply]

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

end
