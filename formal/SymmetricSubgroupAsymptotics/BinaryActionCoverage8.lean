import SymmetricSubgroupAsymptotics.BinaryMenuRoots
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T1
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T2
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T3
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T4
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T5
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T6
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T7
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T8
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T9
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T10
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T11
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T15
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T16
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T17
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T18
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T19
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T20
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T21
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T22
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T26
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T27
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T28
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T29
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T30
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T31
import SymmetricSubgroupAsymptotics.BinaryActionChildren8T35

/-! Complete original-point binary action coverage in width 8.
Normal-state acceptance is a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionRegistry8

theorem complete (H : Subgroup (Equiv.Perm (Fin 8)))
    (hH : IsPGroup 2 H) (ht : PermutationSubgroupTransitive H) :
    ActionRegistryCovered actions H := by
  apply permutation_pGroup_action_registry_complete actions BinaryMenuRoot8.sylow
    25 ?_ ?_ H hH ht
  · rw [BinaryMenuRoot8.sylow_eq]
    change Subgroup.closure (Set.range BinaryMenuCayley8T35.generators) = _
    have he : BinaryMenuCayley8T35.generators = BinaryMenuRoot8.generators := by decide +kernel
    rw [he]
  · intro i K hlt hindex htrans
    fin_cases i
    · exact BinaryActionChildren8T1.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T2.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T3.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T4.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T5.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T6.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T7.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T8.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T9.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T10.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T11.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T15.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T16.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T17.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T18.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T19.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T20.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T21.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T22.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T26.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T27.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T28.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T29.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T30.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T31.children K hlt.le hindex htrans
    · exact BinaryActionChildren8T35.children K hlt.le hindex htrans

end SymmetricSubgroupAsymptotics.BinaryActionRegistry8
