import SymmetricSubgroupAsymptotics.BinaryPairFrameSignIsotypes
import SymmetricSubgroupAsymptotics.BinaryPairFrameTernaryUniformCyclic

/-!
# Cyclic ternary pair modules at the high-sign residual thresholds

At six pair coordinates, two realized binary signs force every sign fibre
to have size one, two, or three.  At twelve coordinates, three realized
signs force size one, two, three, or four.  The power-of-two and size-three
fibre theorems therefore cover every isotype.  The generic Clifford
assembly then makes every invariant submodule of the full signed ternary
module, and of its contragredient, cyclic.

At eighteen coordinates, six realized signs again force fibre size at most
three, so the same argument applies there as well.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

private theorem signFiber_uniform_one_of_card_one_two_three
    [Finite X] [Finite I]
    (htrans : MulAction.IsPretransitive G X)
    (chi : CoordinateSign F)
    (hcard : Nat.card {i : I // coordinateSign F i = chi} = 1 ∨
      Nat.card {i : I // coordinateSign F i = chi} = 2 ∨
      Nat.card {i : I // coordinateSign F i = chi} = 3) :
    UniformSubrepresentationGeneratorBound
      (signFiberRepresentation F chi) 1 := by
  rcases hcard with hcard | hcard | hcard
  · apply signFiber_uniformSubrepresentationGeneratorBound_one
      F htrans chi 0
    simpa using hcard
  · apply signFiber_uniformSubrepresentationGeneratorBound_one
      F htrans chi 1
    simpa using hcard
  · exact signFiber_uniformSubrepresentationGeneratorBound_one_of_card_three
      F htrans chi hcard

private theorem signFiber_uniform_one_of_card_one_two_three_four
    [Finite X] [Finite I]
    (htrans : MulAction.IsPretransitive G X)
    (chi : CoordinateSign F)
    (hcard : Nat.card {i : I // coordinateSign F i = chi} = 1 ∨
      Nat.card {i : I // coordinateSign F i = chi} = 2 ∨
      Nat.card {i : I // coordinateSign F i = chi} = 3 ∨
      Nat.card {i : I // coordinateSign F i = chi} = 4) :
    UniformSubrepresentationGeneratorBound
      (signFiberRepresentation F chi) 1 := by
  rcases hcard with hcard | hcard | hcard | hcard
  · apply signFiber_uniformSubrepresentationGeneratorBound_one
      F htrans chi 0
    simpa using hcard
  · apply signFiber_uniformSubrepresentationGeneratorBound_one
      F htrans chi 1
    simpa using hcard
  · exact signFiber_uniformSubrepresentationGeneratorBound_one_of_card_three
      F htrans chi hcard
  · apply signFiber_uniformSubrepresentationGeneratorBound_one
      F htrans chi 2
    simpa using hcard

/-- Two sign classes at six coordinates make the full signed ternary
contragredient uniformly cyclic. -/
theorem ternarySignedRepresentation_dual_uniform_one_of_six_two_signs
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (hsix : Nat.card I = 6)
    (htwo : 2 ≤ Nat.card (CoordinateSign F)) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 1 := by
  apply ternarySignedRepresentation_dual_uniformSubrepresentationGeneratorBound_one
    F htrans
  intro chi
  let i := coordinateSignRepresentative F chi
  have hcases := coordinateSign_fibre_card_cases_six
    F htrans hsix htwo i
  have heq : coordinateSign F i = chi :=
    coordinateSignRepresentative_spec F chi
  have hcases' : Nat.card {j : I // coordinateSign F j = chi} = 1 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 2 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 3 := by
    simpa only [heq] using hcases
  exact signFiber_uniform_one_of_card_one_two_three F htrans chi hcases'

/-- Three sign classes at twelve coordinates make the full signed ternary
contragredient uniformly cyclic. -/
theorem ternarySignedRepresentation_dual_uniform_one_of_twelve_three_signs
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwelve : Nat.card I = 12)
    (hthree : 3 ≤ Nat.card (CoordinateSign F)) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 1 := by
  apply ternarySignedRepresentation_dual_uniformSubrepresentationGeneratorBound_one
    F htrans
  intro chi
  let i := coordinateSignRepresentative F chi
  have hcases := coordinateSign_fibre_card_cases_twelve
    F htrans htwelve hthree i
  have heq : coordinateSign F i = chi :=
    coordinateSignRepresentative_spec F chi
  have hcases' : Nat.card {j : I // coordinateSign F j = chi} = 1 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 2 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 3 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 4 := by
    simpa only [heq] using hcases
  exact signFiber_uniform_one_of_card_one_two_three_four
    F htrans chi hcases'

/-- Six sign classes at eighteen coordinates make the full signed ternary
contragredient uniformly cyclic. -/
theorem ternarySignedRepresentation_dual_uniform_one_of_eighteen_six_signs
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (heighteen : Nat.card I = 18)
    (hsix : 6 ≤ Nat.card (CoordinateSign F)) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 1 := by
  apply ternarySignedRepresentation_dual_uniformSubrepresentationGeneratorBound_one
    F htrans
  intro chi
  let i := coordinateSignRepresentative F chi
  have hcases := coordinateSign_fibre_card_cases_eighteen
    F htrans heighteen hsix i
  have heq : coordinateSign F i = chi :=
    coordinateSignRepresentative_spec F chi
  have hcases' : Nat.card {j : I // coordinateSign F j = chi} = 1 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 2 ∨
      Nat.card {j : I // coordinateSign F j = chi} = 3 := by
    simpa only [heq] using hcases
  exact signFiber_uniform_one_of_card_one_two_three F htrans chi hcases'

/-- Combined high-sign interface used by the degree-three six/twelve
capacity-one owner. -/
theorem ternarySignedRepresentation_dual_uniform_one_of_six_or_twelve
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (hsize :
      (Nat.card I = 6 ∧ 2 ≤ Nat.card (CoordinateSign F)) ∨
      (Nat.card I = 12 ∧ 3 ≤ Nat.card (CoordinateSign F))) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 1 := by
  rcases hsize with ⟨hsix, htwo⟩ | ⟨htwelve, hthree⟩
  · exact ternarySignedRepresentation_dual_uniform_one_of_six_two_signs
      F htrans hsix htwo
  · exact ternarySignedRepresentation_dual_uniform_one_of_twelve_three_signs
      F htrans htwelve hthree

/-- Combined high-sign interface for all three post-four residual block
counts. -/
theorem ternarySignedRepresentation_dual_uniform_one_of_six_twelve_or_eighteen
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (hsize :
      (Nat.card I = 6 ∧ 2 ≤ Nat.card (CoordinateSign F)) ∨
      (Nat.card I = 12 ∧ 3 ≤ Nat.card (CoordinateSign F)) ∨
      (Nat.card I = 18 ∧ 6 ≤ Nat.card (CoordinateSign F))) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 1 := by
  rcases hsize with ⟨hsix, htwo⟩ | ⟨htwelve, hthree⟩ | ⟨heighteen, hsix⟩
  · exact ternarySignedRepresentation_dual_uniform_one_of_six_two_signs
      F htrans hsix htwo
  · exact ternarySignedRepresentation_dual_uniform_one_of_twelve_three_signs
      F htrans htwelve hthree
  · exact ternarySignedRepresentation_dual_uniform_one_of_eighteen_six_signs
      F htrans heighteen hsix

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
