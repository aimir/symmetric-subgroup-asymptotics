import SymmetricSubgroupAsymptotics.BinaryGeneratorRegistry
import SymmetricSubgroupAsymptotics.BinaryMenuCayley16T780
import SymmetricSubgroupAsymptotics.BinaryMenuCayley16T781
import SymmetricSubgroupAsymptotics.BinaryMenuCayley16T788
import SymmetricSubgroupAsymptotics.BinaryMenuCayley16T791
import SymmetricSubgroupAsymptotics.BinaryMenuCayley16T797
import SymmetricSubgroupAsymptotics.BinaryMenuCayley16T1086

/-! Exact generated target actions for all index-two children of b16_1086. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneratorMenu16T1086

def actions (k : Fin 6) : Subgroup (Equiv.Perm (Fin 16)) :=
  ![Subgroup.closure (Set.range BinaryMenuCayley16T780.generators),Subgroup.closure (Set.range BinaryMenuCayley16T781.generators),Subgroup.closure (Set.range BinaryMenuCayley16T788.generators),Subgroup.closure (Set.range BinaryMenuCayley16T791.generators),Subgroup.closure (Set.range BinaryMenuCayley16T797.generators),Subgroup.closure (Set.range BinaryMenuCayley16T1086.generators)] k

def registry : GeneratedPermutationRegistry actions where
  generatorCount k := ![5,5,5,5,4,4] k
  generators :=
    Fin.cases BinaryMenuCayley16T780.generators (Fin.cases BinaryMenuCayley16T781.generators (Fin.cases BinaryMenuCayley16T788.generators (Fin.cases BinaryMenuCayley16T791.generators (Fin.cases BinaryMenuCayley16T797.generators (Fin.cases BinaryMenuCayley16T1086.generators ((fun i => Fin.elim0 i)))))))
  generated_eq := by
    intro k
    fin_cases k <;> rfl
  order k := ![512,512,512,512,512,1024] k
  card_eq := by
    intro k
    fin_cases k
    · exact BinaryMenuCayley16T780.exact_card
    · exact BinaryMenuCayley16T781.exact_card
    · exact BinaryMenuCayley16T788.exact_card
    · exact BinaryMenuCayley16T791.exact_card
    · exact BinaryMenuCayley16T797.exact_card
    · exact BinaryMenuCayley16T1086.exact_card

end SymmetricSubgroupAsymptotics.BinaryGeneratorMenu16T1086
