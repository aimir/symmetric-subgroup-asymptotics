import SymmetricSubgroupAsymptotics.DerivedWordCentralizerCertificate
import SymmetricSubgroupAsymptotics.PrimeNormalHeadCentralizer
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1082

/-! A selected centralizer inside the actual derived subgroup bounds the
relative heads of all original normal subgroups in that derived subgroup.
The original conjugator uses Lean tuple indices [3]. The checked
derived-word certificate supplies every actual derived row; the finite
implication below covers every row commuting with that same conjugator.
No normal subgroup enumeration or ambient-group table is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original

def conjugator : Original :=
  closureGenerators BinaryActionData16.node1082Generators 3

private def ambientConjugator : Equiv.Perm (Fin 16) :=
  BinaryActionData16.node1082Generators 3

private theorem conjugator_coe :
    (conjugator : Equiv.Perm (Fin 16)) = ambientConjugator := rfl

private def select (j : Fin 8) : Fin 16 :=
  ![0, 1, 3, 4, 6, 7, 10, 13] j

private def code (i : Fin 16) : Fin 8 :=
  ![0, 1, 0, 2, 3, 0, 4, 5,
    0, 0, 6, 0, 0, 7, 0, 0] i

private theorem row_cover : ∀ i : Fin 16,
    (∀ x : Fin 16,
      BinaryCarrierDerivedOrder16T1082.ambientRows i (ambientConjugator x) =
        ambientConjugator (BinaryCarrierDerivedOrder16T1082.ambientRows i x)) →
    select (code i) = i := by
  decide +kernel

/-- This is the literal centralizer intersection inside the original action. -/
theorem centralizer_card_le :
    Nat.card ↥(commutator Original ⊓
      Subgroup.centralizer ({conjugator} : Set Original)) ≤ 8 := by
  apply BinaryCarrierDerivedOrder16T1082.certificate.card_centralizer_le_of_pointwise_row_code
    conjugator select code
  intro i hi
  apply row_cover i
  intro x
  simpa only [BinaryCarrierDerivedOrder16T1082.certificate_elements_coe,
    conjugator_coe] using hi x

/-- The maximum includes every subgroup normal under the whole original group. -/
theorem derivedNormalRank_le : primeDerivedNormalRank 2 Original ≤ 3 := by
  apply primeDerivedNormalRank_le_of_centralizer_card_le 2 conjugator 3
  simpa only [show (2 : ℕ) ^ 3 = 8 from by decide] using centralizer_card_le

end SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1082
