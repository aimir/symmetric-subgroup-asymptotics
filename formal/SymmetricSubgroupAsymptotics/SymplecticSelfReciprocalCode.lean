import SymmetricSubgroupAsymptotics.SymplecticCharacteristicReciprocity
import SymmetricSubgroupAsymptotics.MonicSelfReciprocalPolynomialCount

/-! The characteristic polynomials of the actual symplectic group
have at most `q^r` possibilities. This bounds polynomial values, not
conjugacy classes: multiplicities within each polynomial are separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SymplecticSelfReciprocalCode
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] [CharP K 2]

def charpolyFamily (A : Matrix.symplecticGroup I K) :
    MonicSelfReciprocalPolynomialCount.Family K (Fintype.card I) := by
  refine ⟨(A : Matrix (I⊕I) (I⊕I) K).charpoly, Matrix.charpoly_monic _, ?_,
    SymplecticCharacteristicReciprocity.charpoly_reverse A⟩
  simpa only [Fintype.card_sum, two_mul] using
    (Matrix.charpoly_natDegree_eq_dim (A : Matrix (I⊕I) (I⊕I) K))

theorem charpoly_code_eq_iff (A B : Matrix.symplecticGroup I K) :
    MonicSelfReciprocalPolynomialCount.code K (charpolyFamily A) =
        MonicSelfReciprocalPolynomialCount.code K (charpolyFamily B) ↔
      (A : Matrix (I⊕I) (I⊕I) K).charpoly =
        (B : Matrix (I⊕I) (I⊕I) K).charpoly := by
  constructor
  · intro h
    exact congrArg Subtype.val
      (MonicSelfReciprocalPolynomialCount.code_injective K _ h)
  · intro h
    apply congrArg (MonicSelfReciprocalPolynomialCount.code K)
    exact Subtype.ext h

def rangeToFamily
    (p : Set.range (fun A : Matrix.symplecticGroup I K =>
      (A : Matrix (I⊕I) (I⊕I) K).charpoly)) :
    MonicSelfReciprocalPolynomialCount.Family K (Fintype.card I) := by
  refine ⟨p.1, ?_⟩
  rcases p.2 with ⟨A, hA⟩
  rw [←hA]
  exact (charpolyFamily A).2

theorem card_charpoly_range_le [Finite K] :
    Nat.card (Set.range (fun A : Matrix.symplecticGroup I K =>
      (A : Matrix (I⊕I) (I⊕I) K).charpoly)) ≤ Nat.card K ^ Fintype.card I := by
  apply (Nat.card_le_card_of_injective rangeToFamily ?_).trans
    (MonicSelfReciprocalPolynomialCount.card_le K _)
  intro p q h
  apply Subtype.ext
  exact congrArg
    (fun f : MonicSelfReciprocalPolynomialCount.Family K (Fintype.card I) => f.1) h

end SymmetricSubgroupAsymptotics.SymplecticSelfReciprocalCode
