import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTupleCompletion
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveScalarRelationWords

/-! Symbolic packed point shadow for original five-tuple completion. Only
previously checked50 original transversal seed maps are used; no new row
binding or finite group table occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTuplePackedCompletion
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelveFiveTransversalCover
open CFSGMathieuTwelveFiveTupleCompletion CFSGMathieuTwelveTransversalSeedImages
open CFSGMathieuTwelvePackedPointMaps CFSGMathieuTwelveScalarRelationWords

def rawAddress2 (a b : ℕ) : ℕ := packedFirstInverse a b
def rawAddress3 (a b c : ℕ) : ℕ :=
  packedSecondInverse (rawAddress2 a b) (packedFirstInverse a c)
def rawAddress4 (a b c d : ℕ) : ℕ :=
  packedThirdInverse (rawAddress3 a b c)
    (packedSecondInverse (rawAddress2 a b) (packedFirstInverse a d))
def rawAddress5 (a b c d e : ℕ) : ℕ :=
  packedFourthInverse (rawAddress4 a b c d)
    (packedThirdInverse (rawAddress3 a b c)
      (packedSecondInverse (rawAddress2 a b) (packedFirstInverse a e)))

def rawComplete (a b c d e p : ℕ) : ℕ :=
  packedCandidateForward a (rawAddress2 a b) (rawAddress3 a b c)
    (rawAddress4 a b c d) (rawAddress5 a b c d e) p

def rawCompleteInverse (a b c d e p : ℕ) : ℕ :=
  packedCandidateInverse a (rawAddress2 a b) (rawAddress3 a b c)
    (rawAddress4 a b c d) (rawAddress5 a b c d e) p

def tupleCode (t : Fin 5 ↪ Fin 12) : Code :=
  ((t 0,address2 t),(address3 t,(address4 t,address5 t)))

theorem complete_eq_decode (t : Fin 5 ↪ Fin 12) : complete t = decode (tupleCode t) := by
  unfold complete prefix4 prefix3 prefix2 prefix1 tupleCode decode
  rfl

theorem rawAddress2_eq (t : Fin 5 ↪ Fin 12) :
    rawAddress2 (t 0).val (t 1).val = (address2 t).val.val := by
  change packedFirstInverse (t 0).val (t 1).val = ((first (t 0)).val.symm (t 1)).val
  rw [first_coe_eq]
  exact (first_point_eq (t 0) (t 1)).2

private theorem prefix2_inverse (t : Fin 5 ↪ Fin 12) (p : Fin 12) :
    packedSecondInverse (rawAddress2 (t 0).val (t 1).val) (packedFirstInverse (t 0).val (p.val)) = ((prefix2 t).val.symm p).val := by
  rw [rawAddress2_eq]
  rw [(first_point_eq (t 0) (p)).2]
  rw [(second_point_eq ((address2 t).val) ((firstSeed (t 0)).symm (p))).2]
  simp only [prefix2,prefix1,Subgroup.coe_mul,first_coe_eq,second_coe_eq]
  rfl

theorem rawAddress3_eq (t : Fin 5 ↪ Fin 12) :
    rawAddress3 (t 0).val (t 1).val (t 2).val = (address3 t).val.val := by
  exact prefix2_inverse t (t 2)

private theorem prefix3_inverse (t : Fin 5 ↪ Fin 12) (p : Fin 12) :
    packedThirdInverse (rawAddress3 (t 0).val (t 1).val (t 2).val) (packedSecondInverse (rawAddress2 (t 0).val (t 1).val) (packedFirstInverse (t 0).val (p.val))) = ((prefix3 t).val.symm p).val := by
  rw [rawAddress2_eq]
  rw [rawAddress3_eq]
  rw [(first_point_eq (t 0) (p)).2]
  rw [(second_point_eq ((address2 t).val) ((firstSeed (t 0)).symm (p))).2]
  rw [(third_point_eq ((address3 t).val) ((secondSeed ((address2 t).val)).symm ((firstSeed (t 0)).symm (p)))).2]
  simp only [prefix3,prefix2,prefix1,Subgroup.coe_mul,first_coe_eq,second_coe_eq,third_coe_eq]
  rfl

theorem rawAddress4_eq (t : Fin 5 ↪ Fin 12) :
    rawAddress4 (t 0).val (t 1).val (t 2).val (t 3).val = (address4 t).val.val := by
  exact prefix3_inverse t (t 3)

private theorem prefix4_inverse (t : Fin 5 ↪ Fin 12) (p : Fin 12) :
    packedFourthInverse (rawAddress4 (t 0).val (t 1).val (t 2).val (t 3).val) (packedThirdInverse (rawAddress3 (t 0).val (t 1).val (t 2).val) (packedSecondInverse (rawAddress2 (t 0).val (t 1).val) (packedFirstInverse (t 0).val (p.val)))) = ((prefix4 t).val.symm p).val := by
  rw [rawAddress2_eq]
  rw [rawAddress3_eq]
  rw [rawAddress4_eq]
  rw [(first_point_eq (t 0) (p)).2]
  rw [(second_point_eq ((address2 t).val) ((firstSeed (t 0)).symm (p))).2]
  rw [(third_point_eq ((address3 t).val) ((secondSeed ((address2 t).val)).symm ((firstSeed (t 0)).symm (p)))).2]
  rw [(fourth_point_eq ((address4 t).val) ((thirdSeed ((address3 t).val)).symm ((secondSeed ((address2 t).val)).symm ((firstSeed (t 0)).symm (p))))).2]
  simp only [prefix4,prefix3,prefix2,prefix1,Subgroup.coe_mul,first_coe_eq,second_coe_eq,third_coe_eq,fourth_coe_eq]
  rfl

theorem rawAddress5_eq (t : Fin 5 ↪ Fin 12) :
    rawAddress5 (t 0).val (t 1).val (t 2).val (t 3).val (t 4).val = (address5 t).val.val := by
  exact prefix4_inverse t (t 4)

theorem rawComplete_eq (t : Fin 5 ↪ Fin 12) (p : Fin 12) :
    rawComplete (t 0).val (t 1).val (t 2).val (t 3).val (t 4).val p.val =
      ((complete t).val p).val := by
  unfold rawComplete
  rw [rawAddress2_eq,rawAddress3_eq,rawAddress4_eq,rawAddress5_eq,
    complete_eq_decode,decode_coe_eq]
  exact candidateForward_point_eq (tupleCode t) p

theorem rawCompleteInverse_eq (t : Fin 5 ↪ Fin 12) (p : Fin 12) :
    rawCompleteInverse (t 0).val (t 1).val (t 2).val (t 3).val (t 4).val p.val =
      ((complete t).val.symm p).val := by
  unfold rawCompleteInverse
  rw [rawAddress2_eq,rawAddress3_eq,rawAddress4_eq,rawAddress5_eq,
    complete_eq_decode,decode_coe_eq]
  exact candidateInverse_point_eq (tupleCode t) p

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTuplePackedCompletion
