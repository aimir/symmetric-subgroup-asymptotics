import SymmetricSubgroupAsymptotics.BinaryPairFrameSignFiberCyclic
import SymmetricSubgroupAsymptotics.PermutationalWreathFunctionCoinduced
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-!
# Three generators on a six-coordinate sign fibre

The literal sign-fibre representation is the full function representation
of its transitive stabilizer wreath action.  Evaluation at one coordinate
embeds it in the induced module from the one-dimensional local action.
Tracey's half-dimension theorem therefore gives three generators for every
invariant submodule when the fibre has size six.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

open OddMarkerTernaryChart
open PermutationalWreathProduct

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- Tracey's half-dimension theorem gives a uniform three-generator bound
on a transitive six-coordinate sign fibre. -/
theorem signFiber_uniformSubrepresentationGeneratorBound_three_of_card_six
    [Finite X] [Finite I]
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (htrans : MulAction.IsPretransitive G X)
    (chi : CoordinateSign F)
    (hcard : Nat.card {i : I // coordinateSign F i = chi} = 6) :
    UniformSubrepresentationGeneratorBound
      (signFiberRepresentation F chi) 3 := by
  let J := {i : I // coordinateSign F i = chi}
  let A := MulAction.stabilizer G chi
  letI : MulAction.IsPretransitive A J :=
    coordinateSignFiber_stabilizer_pretransitive F htrans chi
  obtain ⟨i0, hi0⟩ := coordinateSign_surjective F chi
  let i0J : J := ⟨i0, hi0⟩
  let rho : A →* PermutationalWreathProduct
      (Multiplicative (ZMod 2)) A J :=
    signFiberWreathEmbedding F chi
  let sigma : Representation (ZMod 3) (Multiplicative (ZMod 2)) (ZMod 3) :=
    ternarySignRepresentation
  let H := FunctionCoinduced.stabilizer rho i0J
  have hHeq : H = MulAction.stabilizer A i0J := by
    ext u
    rfl
  have hHindex : H.index = 6 := by
    rw [hHeq, MulAction.index_stabilizer_of_transitive A i0J]
    exact hcard
  letI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  let local := FunctionCoinduced.localRepresentation rho sigma i0J
  have hind := hTraceyHalf 3 A H (by omega) (ZMod 3) local
  have hind3 : UniformSubrepresentationGeneratorBound
      (Representation.ind H.subtype local) 3 := by
    simpa only [Module.finrank_self, hHindex, one_mul] using hind
  have htop : Function.Surjective
      ((rightHom (D := Multiplicative (ZMod 2)) (Q := A) (I := J)).comp rho) := by
    intro u
    exact ⟨u, rfl⟩
  have hfull := hind3.of_injective
    (FunctionCoinduced.toInduced rho sigma i0J)
    (FunctionCoinduced.toInduced_injective rho sigma i0J htop)
  simpa only [FunctionCoinduced.fullRepresentation, rho, sigma, A, J,
    signFiberRepresentation] using hfull

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
