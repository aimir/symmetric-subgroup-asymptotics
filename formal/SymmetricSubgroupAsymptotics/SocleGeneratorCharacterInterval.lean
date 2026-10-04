import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteCharacterIntervalSource

/-!
# From socle generators to a complete character interval

This is the reusable bridge between the structural affine argument and the
already-closed complete-source counting theorem.  Normals containing `E` are
charged once to `U / E`.  For every other literal normal quotient, a bound on
normal generators of its socle is converted by Zmud's published theorem into
a fixed jointly faithful tuple.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private abbrev LiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- Pure structural data for a correlated character interval.  There is no
counting or asymptotic conclusion in this record. -/
structure SocleGeneratorCharacterIntervalData {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) : Type 1 where
  E : Subgroup U
  [E_normal : E.Normal]
  quotientDegree : ℕ
  quotientAction : (U ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  slots : ℕ
  quotientSocleGenerators : ∀ N : LiteralNormalAxis U, ¬ E ≤ N.1 →
    SocleNormalGeneratorBound (U ⧸ N.1) slots

attribute [instance] SocleGeneratorCharacterIntervalData.E_normal

namespace SocleGeneratorCharacterIntervalData

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (D : SocleGeneratorCharacterIntervalData U)

/-- Apply Zmud on every literal axis below `E`, chosen before the
complementary source is inspected. -/
noncomputable def toCompleteCharacterIntervalData
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    CompleteCharacterIntervalData U where
  E := D.E
  quotientDegree := D.quotientDegree
  quotientAction := D.quotientAction
  quotientAction_injective := D.quotientAction_injective
  theta := (D.slots : ℝ) * (Real.logb 2 5 / 3)
  quotientCertificate := fun N hN =>
    hZmud.generalCertificate (D.quotientSocleGenerators N hN)
  quotientCertificate_mixed := by
    intro N hN
    rfl
  quotientCertificate_slope := by
    intro N hN
    rw [ZmudFaithfulCharacterTupleInput.generalCertificate_slope]

@[simp] theorem toCompleteCharacterIntervalData_E
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.toCompleteCharacterIntervalData hZmud).E = D.E := rfl

@[simp] theorem toCompleteCharacterIntervalData_quotientDegree
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.toCompleteCharacterIntervalData hZmud).quotientDegree =
      D.quotientDegree := rfl

@[simp] theorem toCompleteCharacterIntervalData_theta
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.toCompleteCharacterIntervalData hZmud).theta =
      (D.slots : ℝ) * (Real.logb 2 5 / 3) := rfl

end SocleGeneratorCharacterIntervalData
end SymmetricSubgroupAsymptotics

end
