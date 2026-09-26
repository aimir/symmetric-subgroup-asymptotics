import SymmetricSubgroupAsymptotics.DerivedWordCentralizerCertificate
import SymmetricSubgroupAsymptotics.PrimeNormalHeadCentralizer
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1332

/-! A selected centralizer inside the actual derived subgroup bounds the
relative heads of all original normal subgroups in that derived subgroup.
The original conjugator uses Lean tuple indices [2]. The checked
derived-word certificate supplies every actual derived row; the finite
implication below covers every row commuting with that same conjugator.
No normal subgroup enumeration or ambient-group table is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original

def conjugator : Original :=
  closureGenerators BinaryActionData16.node1332Generators 2

private def ambientConjugator : Equiv.Perm (Fin 16) :=
  BinaryActionData16.node1332Generators 2

private theorem conjugator_coe :
    (conjugator : Equiv.Perm (Fin 16)) = ambientConjugator := rfl

private def select (j : Fin 16) : Fin 64 :=
  ![0, 1, 3, 8, 14, 28, 41, 43,
    46, 48, 49, 51, 53, 56, 58, 59] j

private def code (i : Fin 64) : Fin 16 :=
  ![0, 1, 0, 2, 0, 0, 0, 0,
    3, 0, 0, 0, 0, 0, 4, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 5, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 6, 0, 7, 0, 0, 8, 0,
    9, 10, 0, 11, 0, 12, 0, 0,
    13, 0, 14, 15, 0, 0, 0, 0] i

private theorem row_cover : ∀ i : Fin 64,
    (∀ x : Fin 16,
      BinaryCarrierDerivedOrder16T1332.ambientRows i (ambientConjugator x) =
        ambientConjugator (BinaryCarrierDerivedOrder16T1332.ambientRows i x)) →
    select (code i) = i := by
  decide +kernel

/-- This is the literal centralizer intersection inside the original action. -/
theorem centralizer_card_le :
    Nat.card ↥(commutator Original ⊓
      Subgroup.centralizer ({conjugator} : Set Original)) ≤ 16 := by
  apply BinaryCarrierDerivedOrder16T1332.certificate.card_centralizer_le_of_pointwise_row_code
    conjugator select code
  intro i hi
  apply row_cover i
  intro x
  simpa only [BinaryCarrierDerivedOrder16T1332.certificate_elements_coe,
    conjugator_coe] using hi x

/-- The maximum includes every subgroup normal under the whole original group. -/
theorem derivedNormalRank_le : primeDerivedNormalRank 2 Original ≤ 4 := by
  apply primeDerivedNormalRank_le_of_centralizer_card_le 2 conjugator 4
  simpa only [show (2 : ℕ) ^ 4 = 16 from by decide] using centralizer_card_le

end SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1332
