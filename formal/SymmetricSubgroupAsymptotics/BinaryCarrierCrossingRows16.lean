import SymmetricSubgroupAsymptotics.BinaryCarrierCrossingCapacity16
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory

/-! Exact rows for every crossing normal of the four original pair-family
masters. The same literal normal supplies all six fields. This is crossing
coverage only, not coverage of all normals or a bound on their weights. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat BinaryMarkedGoursatPeel

namespace BinaryCarrierCrossingRows

/-- b is the logarithmic order of the actual derived intersection. -/
def row (b w : ℕ) : JointCapacityRow := ⟨w, b+w, 2, 2, (3-w : ℕ), 1⟩

private theorem actualRow_eq_of_fields {A : BinaryCarrierWord.Factor}
    (N : NormalAxis A.Carrier) (b w : ℕ)
    (hk : head N = w) (hn : Nat.card N.1 = 2^(b+w))
    (hm : derivedHead N = 2) (ha : radicalHead N = 2)
    (hc : Nat.card (Subgroup.center (A.Carrier ⧸ N.1)) = 2^(3-w))
    (hg : Nat.card (commutator (A.Carrier ⧸ N.1)) = 2) :
    BinaryCarrierWord.actualRow (A := A) N = row b w := by
  have hn' : orderLog N = b+w := by
    change Nat.log 2 (Nat.card N.1) = _
    rw [hn, Nat.log_pow (by decide)]
  have hc' : centerSlope N = 3-w := by
    change Nat.log 2 (Nat.card (Subgroup.center (A.Carrier ⧸ N.1))) = _
    rw [hc, Nat.log_pow (by decide)]
  have hg' : derivedSlope N = 1 := by
    change Nat.log 2 (Nat.card (commutator (A.Carrier ⧸ N.1))) = _
    rw [hg]
    decide
  simp only [BinaryCarrierWord.actualRow, row, hk, hn', hm, ha, hc', hg', Nat.cast_one]

end BinaryCarrierCrossingRows

namespace BinaryCarrierCrossingRows16T1082

abbrev Original := BinaryCarrierCrossing16T1082.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1082.original_isPGroup

/-- The exact row depends only on the actual image dimension, which is one or two. -/
theorem actualRow_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N =
      BinaryCarrierCrossingRows.row 3 (Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
  obtain ⟨hw1, hw2, hB, hc, hg⟩ :=
    BinaryCarrierCrossing16T1082.exact_quotient_invariants N.1 hnotND hnotDN
  have hB' : Nat.card ↥(N.1 ⊓ commutator Original) = 2^3 := by
    rw [BinaryCarrierDerivedOrder16T1082.card_commutator] at hB
    change 2 * Nat.card ↥(N.1 ⊓ commutator Original) = 16 at hB
    omega
  have hn := primeDerivedImage_pow_finrank_mul_intersection 2
    BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator N.1
  rw [hB'] at hn
  have hn' : Nat.card N.1 = 2^(3 + Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
    rw [Nat.pow_add, Nat.mul_comm]
    exact hn.symm
  apply BinaryCarrierCrossingRows.actualRow_eq_of_fields (A := factor) N 3 _
  · exact BinaryCarrierCrossing16T1082.relative_head_eq_image N.1 hnotND hnotDN
  · exact hn'
  · exact BinaryCarrierCrossingCapacity16T1082.intersection_normalHeadMax_eq_two N.1 hnotND hnotDN
  · exact BinaryCarrierCrossingCapacity16T1082.second_radical_head_eq_two N.1 hnotND hnotDN
  · exact hc
  · exact hg

/-- Every original crossing normal belongs to these two rows; this does not
assert that both rows are realized, nor merge different normal axes. -/
theorem actualRow_two_cases (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 1 ∨
      BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 2 := by
  have h := BinaryCarrierCrossing16T1082.exact_quotient_invariants N.1 hnotND hnotDN
  have hw1 : 1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) := h.1
  have hw2 : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) ≤ 2 := h.2.1
  have hw : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 1 ∨
      Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 2 := by omega
  rw [actualRow_eq N hnotND hnotDN]
  rcases hw with hw | hw
  · exact Or.inl (congrArg _ hw)
  · exact Or.inr (congrArg _ hw)

end BinaryCarrierCrossingRows16T1082

namespace BinaryCarrierCrossingRows16T1083

abbrev Original := BinaryCarrierCrossing16T1083.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1083.original_isPGroup

/-- The exact row depends only on the actual image dimension, which is one or two. -/
theorem actualRow_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N =
      BinaryCarrierCrossingRows.row 3 (Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
  obtain ⟨hw1, hw2, hB, hc, hg⟩ :=
    BinaryCarrierCrossing16T1083.exact_quotient_invariants N.1 hnotND hnotDN
  have hB' : Nat.card ↥(N.1 ⊓ commutator Original) = 2^3 := by
    rw [BinaryCarrierDerivedOrder16T1083.card_commutator] at hB
    change 2 * Nat.card ↥(N.1 ⊓ commutator Original) = 16 at hB
    omega
  have hn := primeDerivedImage_pow_finrank_mul_intersection 2
    BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator N.1
  rw [hB'] at hn
  have hn' : Nat.card N.1 = 2^(3 + Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
    rw [Nat.pow_add, Nat.mul_comm]
    exact hn.symm
  apply BinaryCarrierCrossingRows.actualRow_eq_of_fields (A := factor) N 3 _
  · exact BinaryCarrierCrossing16T1083.relative_head_eq_image N.1 hnotND hnotDN
  · exact hn'
  · exact BinaryCarrierCrossingCapacity16T1083.intersection_normalHeadMax_eq_two N.1 hnotND hnotDN
  · exact BinaryCarrierCrossingCapacity16T1083.second_radical_head_eq_two N.1 hnotND hnotDN
  · exact hc
  · exact hg

/-- Every original crossing normal belongs to these two rows; this does not
assert that both rows are realized, nor merge different normal axes. -/
theorem actualRow_two_cases (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 1 ∨
      BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 2 := by
  have h := BinaryCarrierCrossing16T1083.exact_quotient_invariants N.1 hnotND hnotDN
  have hw1 : 1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) := h.1
  have hw2 : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) ≤ 2 := h.2.1
  have hw : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 1 ∨
      Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 2 := by omega
  rw [actualRow_eq N hnotND hnotDN]
  rcases hw with hw | hw
  · exact Or.inl (congrArg _ hw)
  · exact Or.inr (congrArg _ hw)

end BinaryCarrierCrossingRows16T1083

namespace BinaryCarrierCrossingRows16T1084

abbrev Original := BinaryCarrierCrossing16T1084.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1084.original_isPGroup

/-- The exact row depends only on the actual image dimension, which is one or two. -/
theorem actualRow_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N =
      BinaryCarrierCrossingRows.row 3 (Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
  obtain ⟨hw1, hw2, hB, hc, hg⟩ :=
    BinaryCarrierCrossing16T1084.exact_quotient_invariants N.1 hnotND hnotDN
  have hB' : Nat.card ↥(N.1 ⊓ commutator Original) = 2^3 := by
    rw [BinaryCarrierDerivedOrder16T1084.card_commutator] at hB
    change 2 * Nat.card ↥(N.1 ⊓ commutator Original) = 16 at hB
    omega
  have hn := primeDerivedImage_pow_finrank_mul_intersection 2
    BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator N.1
  rw [hB'] at hn
  have hn' : Nat.card N.1 = 2^(3 + Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
    rw [Nat.pow_add, Nat.mul_comm]
    exact hn.symm
  apply BinaryCarrierCrossingRows.actualRow_eq_of_fields (A := factor) N 3 _
  · exact BinaryCarrierCrossing16T1084.relative_head_eq_image N.1 hnotND hnotDN
  · exact hn'
  · exact BinaryCarrierCrossingCapacity16T1084.intersection_normalHeadMax_eq_two N.1 hnotND hnotDN
  · exact BinaryCarrierCrossingCapacity16T1084.second_radical_head_eq_two N.1 hnotND hnotDN
  · exact hc
  · exact hg

/-- Every original crossing normal belongs to these two rows; this does not
assert that both rows are realized, nor merge different normal axes. -/
theorem actualRow_two_cases (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 1 ∨
      BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 3 2 := by
  have h := BinaryCarrierCrossing16T1084.exact_quotient_invariants N.1 hnotND hnotDN
  have hw1 : 1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) := h.1
  have hw2 : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) ≤ 2 := h.2.1
  have hw : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 1 ∨
      Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 2 := by omega
  rw [actualRow_eq N hnotND hnotDN]
  rcases hw with hw | hw
  · exact Or.inl (congrArg _ hw)
  · exact Or.inr (congrArg _ hw)

end BinaryCarrierCrossingRows16T1084

namespace BinaryCarrierCrossingRows16T1547

abbrev Original := BinaryCarrierCrossing16T1547.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1547.original_isPGroup

/-- The exact row depends only on the actual image dimension, which is one or two. -/
theorem actualRow_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N =
      BinaryCarrierCrossingRows.row 5 (Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
  obtain ⟨hw1, hw2, hB, hc, hg⟩ :=
    BinaryCarrierCrossing16T1547.exact_quotient_invariants N.1 hnotND hnotDN
  have hB' : Nat.card ↥(N.1 ⊓ commutator Original) = 2^5 := by
    rw [BinaryCarrierDerivedOrder16T1547.card_commutator] at hB
    change 2 * Nat.card ↥(N.1 ⊓ commutator Original) = 64 at hB
    omega
  have hn := primeDerivedImage_pow_finrank_mul_intersection 2
    BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator N.1
  rw [hB'] at hn
  have hn' : Nat.card N.1 = 2^(5 + Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)) := by
    rw [Nat.pow_add, Nat.mul_comm]
    exact hn.symm
  apply BinaryCarrierCrossingRows.actualRow_eq_of_fields (A := factor) N 5 _
  · exact BinaryCarrierCrossing16T1547.relative_head_eq_image N.1 hnotND hnotDN
  · exact hn'
  · exact BinaryCarrierCrossingCapacity16T1547.intersection_normalHeadMax_eq_two N.1 hnotND hnotDN
  · exact BinaryCarrierCrossingCapacity16T1547.second_radical_head_eq_two N.1 hnotND hnotDN
  · exact hc
  · exact hg

/-- Every original crossing normal belongs to these two rows; this does not
assert that both rows are realized, nor merge different normal axes. -/
theorem actualRow_two_cases (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 5 1 ∨
      BinaryCarrierWord.actualRow (A := factor) N = BinaryCarrierCrossingRows.row 5 2 := by
  have h := BinaryCarrierCrossing16T1547.exact_quotient_invariants N.1 hnotND hnotDN
  have hw1 : 1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) := h.1
  have hw2 : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) ≤ 2 := h.2.1
  have hw : Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 1 ∨
      Module.finrank (ZMod 2) (primeDerivedImage 2 N.1) = 2 := by omega
  rw [actualRow_eq N hnotND hnotDN]
  rcases hw with hw | hw
  · exact Or.inl (congrArg _ hw)
  · exact Or.inr (congrArg _ hw)

end BinaryCarrierCrossingRows16T1547

end SymmetricSubgroupAsymptotics
