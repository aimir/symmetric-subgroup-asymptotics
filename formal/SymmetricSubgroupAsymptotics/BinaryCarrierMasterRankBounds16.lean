import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedMasters16
import SymmetricSubgroupAsymptotics.BinaryCarrierAxisCapacity
import SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierRank16T1547

/-! Uniform bounds on both actual heads for every original normal axis
of the five literal degree-sixteen master closures. The centralizer
certificates bound the complete derived-normal maximum, and the checked
evaluation-kernel identities control each original relative radical.
No normal-profile list, axis selection or coverage premise is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat BinaryMarkedGoursatPeel

namespace BinaryCarrierRank16T1082

theorem max_heads_le (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ 3 := by
  rw [BinaryCarrierDerived16T1082.max_eq_derivedHead]
  change primeNormalHeadMax 2 (N.1 ⊓ commutator Original) ≤ 3
  exact (primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator Original ≤ commutator Original from inf_le_right)).trans
      derivedNormalRank_le

theorem max_heads_le_min_orderLog (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ min (orderLog N) 3 :=
  maxHead_le_min_orderLog_rank N 3
    BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator.le derivedNormalRank_le

end BinaryCarrierRank16T1082

namespace BinaryCarrierRank16T1083

theorem max_heads_le (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ 3 := by
  rw [BinaryCarrierDerived16T1083.max_eq_derivedHead]
  change primeNormalHeadMax 2 (N.1 ⊓ commutator Original) ≤ 3
  exact (primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator Original ≤ commutator Original from inf_le_right)).trans
      derivedNormalRank_le

theorem max_heads_le_min_orderLog (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ min (orderLog N) 3 :=
  maxHead_le_min_orderLog_rank N 3
    BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator.le derivedNormalRank_le

end BinaryCarrierRank16T1083

namespace BinaryCarrierRank16T1084

theorem max_heads_le (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ 3 := by
  rw [BinaryCarrierDerived16T1084.max_eq_derivedHead]
  change primeNormalHeadMax 2 (N.1 ⊓ commutator Original) ≤ 3
  exact (primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator Original ≤ commutator Original from inf_le_right)).trans
      derivedNormalRank_le

theorem max_heads_le_min_orderLog (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ min (orderLog N) 3 :=
  maxHead_le_min_orderLog_rank N 3
    BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator.le derivedNormalRank_le

end BinaryCarrierRank16T1084

namespace BinaryCarrierRank16T1332

theorem max_heads_le (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ 4 := by
  rw [BinaryCarrierDerived16T1332.max_eq_derivedHead]
  change primeNormalHeadMax 2 (N.1 ⊓ commutator Original) ≤ 4
  exact (primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator Original ≤ commutator Original from inf_le_right)).trans
      derivedNormalRank_le

theorem max_heads_le_min_orderLog (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ min (orderLog N) 4 :=
  maxHead_le_min_orderLog_rank N 4
    BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator.le derivedNormalRank_le

end BinaryCarrierRank16T1332

namespace BinaryCarrierRank16T1547

theorem max_heads_le (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ 3 := by
  rw [BinaryCarrierDerived16T1547.max_eq_derivedHead]
  change primeNormalHeadMax 2 (N.1 ⊓ commutator Original) ≤ 3
  exact (primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator Original ≤ commutator Original from inf_le_right)).trans
      derivedNormalRank_le

theorem max_heads_le_min_orderLog (N : NormalAxis Original) :
    max (derivedHead N) (radicalHead N) ≤ min (orderLog N) 3 :=
  maxHead_le_min_orderLog_rank N 3
    BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator.le derivedNormalRank_le

end BinaryCarrierRank16T1547

end SymmetricSubgroupAsymptotics
