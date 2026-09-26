import SymmetricSubgroupAsymptotics.BinaryCarrierAboveDerivedRows
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterRankBounds16
import SymmetricSubgroupAsymptotics.BinaryCarrierExactOrders16
import SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierHeadAboveDerived16T1547

/-! Uniform above-derived row bounds for all five literal masters.
The complete derived-normal maximum equals the actual derived head:
the checked centralizer bound supplies one inequality, and the original
derived subgroup itself supplies the other. Existing actual form bounds
control the head of N. No normal catalogue or physical weight is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat BinaryMarkedGoursatPeel
open BinaryCarrierAboveDerivedRows JointCapacityRow

namespace BinaryCarrierAboveDerivedRows16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1082.original_isPGroup

def data : Data factor 4 6 3 where
  kernel := BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator
  derivedCard := by
    simpa only [show (2 : ℕ)^4 = 16 from by decide] using
      BinaryCarrierDerivedOrder16T1082.card_commutator
  evaluationRank := BinaryCarrierExactOrder16T1082.evaluation_finrank
  derivedRank := by
    apply le_antisymm BinaryCarrierRank16T1082.derivedNormalRank_le
    have h : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) ≤
        primeDerivedNormalRank 2 Original :=
      primeRelativeHead_le_normalHeadMax 2 (commutator Original) (commutator Original) le_rfl
    simpa only [BinaryCarrierDerivedRadical16T1082.relative_character_rank] using h
  head_bound := BinaryCarrierHeadAboveDerived16T1082.head_le_max_three_image

theorem imageDimension_le_six (N : Subgroup Original) : imageDimension N ≤ 6 :=
  data.imageDimension_le N

theorem derivedHead_eq_three (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    derivedHead N = 3 := data.derivedHead_eq N hDN

theorem actualRow_boundedBy (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      (row 4 6 3 (imageDimension N.1)) := data.actualRow_boundedBy N hDN

end BinaryCarrierAboveDerivedRows16T1082

namespace BinaryCarrierAboveDerivedRows16T1083

abbrev Original := BinaryCarrierDerivedOrder16T1083.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1083.original_isPGroup

def data : Data factor 4 6 3 where
  kernel := BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator
  derivedCard := by
    simpa only [show (2 : ℕ)^4 = 16 from by decide] using
      BinaryCarrierDerivedOrder16T1083.card_commutator
  evaluationRank := BinaryCarrierExactOrder16T1083.evaluation_finrank
  derivedRank := by
    apply le_antisymm BinaryCarrierRank16T1083.derivedNormalRank_le
    have h : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) ≤
        primeDerivedNormalRank 2 Original :=
      primeRelativeHead_le_normalHeadMax 2 (commutator Original) (commutator Original) le_rfl
    simpa only [BinaryCarrierDerivedRadical16T1083.relative_character_rank] using h
  head_bound := BinaryCarrierHeadAboveDerived16T1083.head_le_max_three_image

theorem imageDimension_le_six (N : Subgroup Original) : imageDimension N ≤ 6 :=
  data.imageDimension_le N

theorem derivedHead_eq_three (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    derivedHead N = 3 := data.derivedHead_eq N hDN

theorem actualRow_boundedBy (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      (row 4 6 3 (imageDimension N.1)) := data.actualRow_boundedBy N hDN

end BinaryCarrierAboveDerivedRows16T1083

namespace BinaryCarrierAboveDerivedRows16T1084

abbrev Original := BinaryCarrierDerivedOrder16T1084.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1084.original_isPGroup

def data : Data factor 4 6 3 where
  kernel := BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator
  derivedCard := by
    simpa only [show (2 : ℕ)^4 = 16 from by decide] using
      BinaryCarrierDerivedOrder16T1084.card_commutator
  evaluationRank := BinaryCarrierExactOrder16T1084.evaluation_finrank
  derivedRank := by
    apply le_antisymm BinaryCarrierRank16T1084.derivedNormalRank_le
    have h : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) ≤
        primeDerivedNormalRank 2 Original :=
      primeRelativeHead_le_normalHeadMax 2 (commutator Original) (commutator Original) le_rfl
    simpa only [BinaryCarrierDerivedRadical16T1084.relative_character_rank] using h
  head_bound := BinaryCarrierHeadAboveDerived16T1084.head_le_max_three_image

theorem imageDimension_le_six (N : Subgroup Original) : imageDimension N ≤ 6 :=
  data.imageDimension_le N

theorem derivedHead_eq_three (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    derivedHead N = 3 := data.derivedHead_eq N hDN

theorem actualRow_boundedBy (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      (row 4 6 3 (imageDimension N.1)) := data.actualRow_boundedBy N hDN

end BinaryCarrierAboveDerivedRows16T1084

namespace BinaryCarrierAboveDerivedRows16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1332.original_isPGroup

def data : Data factor 6 5 4 where
  kernel := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator
  derivedCard := by
    simpa only [show (2 : ℕ)^6 = 64 from by decide] using
      BinaryCarrierDerivedOrder16T1332.card_commutator
  evaluationRank := BinaryCarrierExactOrder16T1332.evaluation_finrank
  derivedRank := by
    apply le_antisymm BinaryCarrierRank16T1332.derivedNormalRank_le
    have h : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) ≤
        primeDerivedNormalRank 2 Original :=
      primeRelativeHead_le_normalHeadMax 2 (commutator Original) (commutator Original) le_rfl
    simpa only [BinaryCarrierDerivedRadical16T1332.relative_character_rank] using h
  head_bound := BinaryCarrierHeadAboveDerived16T1332.head_le_max_four_image

theorem imageDimension_le_five (N : Subgroup Original) : imageDimension N ≤ 5 :=
  data.imageDimension_le N

theorem derivedHead_eq_four (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    derivedHead N = 4 := data.derivedHead_eq N hDN

theorem actualRow_boundedBy (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      (row 6 5 4 (imageDimension N.1)) := data.actualRow_boundedBy N hDN

end BinaryCarrierAboveDerivedRows16T1332

namespace BinaryCarrierAboveDerivedRows16T1547

abbrev Original := BinaryCarrierDerivedOrder16T1547.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1547.original_isPGroup

def data : Data factor 6 6 3 where
  kernel := BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator
  derivedCard := by
    simpa only [show (2 : ℕ)^6 = 64 from by decide] using
      BinaryCarrierDerivedOrder16T1547.card_commutator
  evaluationRank := BinaryCarrierExactOrder16T1547.evaluation_finrank
  derivedRank := by
    apply le_antisymm BinaryCarrierRank16T1547.derivedNormalRank_le
    have h : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (commutator Original)) ≤
        primeDerivedNormalRank 2 Original :=
      primeRelativeHead_le_normalHeadMax 2 (commutator Original) (commutator Original) le_rfl
    simpa only [BinaryCarrierDerivedRadical16T1547.relative_character_rank] using h
  head_bound := BinaryCarrierHeadAboveDerived16T1547.head_le_max_three_image

theorem imageDimension_le_six (N : Subgroup Original) : imageDimension N ≤ 6 :=
  data.imageDimension_le N

theorem derivedHead_eq_three (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    derivedHead N = 3 := data.derivedHead_eq N hDN

theorem actualRow_boundedBy (N : NormalAxis Original) (hDN : commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      (row 6 6 3 (imageDimension N.1)) := data.actualRow_boundedBy N hDN

end BinaryCarrierAboveDerivedRows16T1547

end SymmetricSubgroupAsymptotics
