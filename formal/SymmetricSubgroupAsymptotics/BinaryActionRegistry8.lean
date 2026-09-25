import SymmetricSubgroupAsymptotics.BinaryCharacterRegistry
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T1
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T2
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T4
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T5
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T6
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T7
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T8
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T9
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T10
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T11
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T15
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T16
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T17
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T18
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T19
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T20
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T21
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T22
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T26
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T27
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T28
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T29
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T30
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T31
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T35

/-! Exact original-point code rows for every supplied width-8 action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionRegistry8

def actions (k : Fin 26) : Subgroup (Equiv.Perm (Fin 8)) :=
  ![Subgroup.closure (Set.range BinaryMenuCayley8T1.generators),Subgroup.closure (Set.range BinaryMenuCayley8T2.generators),Subgroup.closure (Set.range BinaryMenuCayley8T3.generators),Subgroup.closure (Set.range BinaryMenuCayley8T4.generators),Subgroup.closure (Set.range BinaryMenuCayley8T5.generators),Subgroup.closure (Set.range BinaryMenuCayley8T6.generators),Subgroup.closure (Set.range BinaryMenuCayley8T7.generators),Subgroup.closure (Set.range BinaryMenuCayley8T8.generators),Subgroup.closure (Set.range BinaryMenuCayley8T9.generators),Subgroup.closure (Set.range BinaryMenuCayley8T10.generators),Subgroup.closure (Set.range BinaryMenuCayley8T11.generators),Subgroup.closure (Set.range BinaryMenuCayley8T15.generators),Subgroup.closure (Set.range BinaryMenuCayley8T16.generators),Subgroup.closure (Set.range BinaryMenuCayley8T17.generators),Subgroup.closure (Set.range BinaryMenuCayley8T18.generators),Subgroup.closure (Set.range BinaryMenuCayley8T19.generators),Subgroup.closure (Set.range BinaryMenuCayley8T20.generators),Subgroup.closure (Set.range BinaryMenuCayley8T21.generators),Subgroup.closure (Set.range BinaryMenuCayley8T22.generators),Subgroup.closure (Set.range BinaryMenuCayley8T26.generators),Subgroup.closure (Set.range BinaryMenuCayley8T27.generators),Subgroup.closure (Set.range BinaryMenuCayley8T28.generators),Subgroup.closure (Set.range BinaryMenuCayley8T29.generators),Subgroup.closure (Set.range BinaryMenuCayley8T30.generators),Subgroup.closure (Set.range BinaryMenuCayley8T31.generators),Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)] k

def registry : LiteralPermutationRegistry actions where
  size k := ![8,8,8,8,8,16,16,16,16,16,16,32,32,32,32,32,32,32,32,64,64,64,64,64,64,128] k
  rows :=
    Fin.cases BinaryMenuCayley8T1.certificate.rows (Fin.cases BinaryMenuCayley8T2.certificate.rows (Fin.cases BinaryMenuCayley8T3.certificate.rows (Fin.cases BinaryMenuCayley8T4.certificate.rows (Fin.cases BinaryMenuCayley8T5.certificate.rows (Fin.cases BinaryMenuCayley8T6.certificate.rows (Fin.cases BinaryMenuCayley8T7.certificate.rows (Fin.cases BinaryMenuCayley8T8.certificate.rows (Fin.cases BinaryMenuCayley8T9.certificate.rows (Fin.cases BinaryMenuCayley8T10.certificate.rows (Fin.cases BinaryMenuCayley8T11.certificate.rows (Fin.cases BinaryMenuCayley8T15.certificate.rows (Fin.cases BinaryMenuCayley8T16.certificate.rows (Fin.cases BinaryMenuCayley8T17.certificate.rows (Fin.cases BinaryMenuCayley8T18.certificate.rows (Fin.cases BinaryMenuCayley8T19.certificate.rows (Fin.cases BinaryMenuCayley8T20.certificate.rows (Fin.cases BinaryMenuCayley8T21.certificate.rows (Fin.cases BinaryMenuCayley8T22.certificate.rows (Fin.cases BinaryMenuCayley8T26.certificate.rows (Fin.cases BinaryMenuCayley8T27.certificate.rows (Fin.cases BinaryMenuCayley8T28.certificate.rows (Fin.cases BinaryMenuCayley8T29.certificate.rows (Fin.cases BinaryMenuCayley8T30.certificate.rows (Fin.cases BinaryMenuCayley8T31.certificate.rows (Fin.cases BinaryMenuCayley8T35.certificate.rows ((fun i => Fin.elim0 i)))))))))))))))))))))))))))
  mem_iff := by
    intro k
    fin_cases k
    · exact BinaryMenuCayley8T1.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T2.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T3.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T4.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T5.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T6.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T7.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T8.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T9.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T10.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T11.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T15.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T16.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T17.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T18.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T19.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T20.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T21.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T22.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T26.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T27.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T28.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T29.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T30.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T31.certificate.mem_closure_iff
    · exact BinaryMenuCayley8T35.certificate.mem_closure_iff

end SymmetricSubgroupAsymptotics.BinaryActionRegistry8
