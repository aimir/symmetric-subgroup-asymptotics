import SymmetricSubgroupAsymptotics.BinaryCarrierAbelianQuotient
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1547

/-! Every normal axis of the five literal degree-sixteen master closures
has second-radical head at most its original derived-normal maximum.
The generator-word certificates identify the actual evaluation kernels;
no order, p-group, normal-menu, or numerical-profile premise is required.
The resulting maximum equality does not identify the two heads. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open FullSubdirectGoursat BinaryMarkedGoursatPeel

namespace BinaryCarrierDerived16T1082

theorem radicalHead_le_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1082Generators))) :
    radicalHead N ≤ derivedHead N :=
  radicalHead_le_derivedHead_of_evaluation_kernel_le N evaluationKernel_eq_commutator.le

theorem max_eq_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1082Generators))) :
    max (derivedHead N) (radicalHead N) = derivedHead N :=
  max_eq_left (radicalHead_le_derivedHead N)

end BinaryCarrierDerived16T1082

namespace BinaryCarrierDerived16T1083

theorem radicalHead_le_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1083Generators))) :
    radicalHead N ≤ derivedHead N :=
  radicalHead_le_derivedHead_of_evaluation_kernel_le N evaluationKernel_eq_commutator.le

theorem max_eq_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1083Generators))) :
    max (derivedHead N) (radicalHead N) = derivedHead N :=
  max_eq_left (radicalHead_le_derivedHead N)

end BinaryCarrierDerived16T1083

namespace BinaryCarrierDerived16T1084

theorem radicalHead_le_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1084Generators))) :
    radicalHead N ≤ derivedHead N :=
  radicalHead_le_derivedHead_of_evaluation_kernel_le N evaluationKernel_eq_commutator.le

theorem max_eq_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1084Generators))) :
    max (derivedHead N) (radicalHead N) = derivedHead N :=
  max_eq_left (radicalHead_le_derivedHead N)

end BinaryCarrierDerived16T1084

namespace BinaryCarrierDerived16T1332

theorem radicalHead_le_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1332Generators))) :
    radicalHead N ≤ derivedHead N :=
  radicalHead_le_derivedHead_of_evaluation_kernel_le N evaluationKernel_eq_commutator.le

theorem max_eq_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1332Generators))) :
    max (derivedHead N) (radicalHead N) = derivedHead N :=
  max_eq_left (radicalHead_le_derivedHead N)

end BinaryCarrierDerived16T1332

namespace BinaryCarrierDerived16T1547

theorem radicalHead_le_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1547Generators))) :
    radicalHead N ≤ derivedHead N :=
  radicalHead_le_derivedHead_of_evaluation_kernel_le N evaluationKernel_eq_commutator.le

theorem max_eq_derivedHead
    (N : NormalAxis (Subgroup.closure (Set.range BinaryActionData16.node1547Generators))) :
    max (derivedHead N) (radicalHead N) = derivedHead N :=
  max_eq_left (radicalHead_le_derivedHead N)

end BinaryCarrierDerived16T1547

end SymmetricSubgroupAsymptotics
