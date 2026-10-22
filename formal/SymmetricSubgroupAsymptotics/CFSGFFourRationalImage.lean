import SymmetricSubgroupAsymptotics.CFSGFFourSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFourthCoefficient

/-! The SAME original F4 rational image lies in the actual E6 Geck Lie
algebra. This proves the needed fourth coefficient only for singleton
long root 2, without imposing a short-root image constraint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSG.Models.Chevalley CFSGExceptionalNormTwoBases
local instance fFourRationalImageDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

private theorem positive_mem_geck (i : Fin 4) :
    positive i∈RootPairing.GeckConstruction.lieAlgebra E6Base := by
  let T := RootPairing.GeckConstruction.lieAlgebra E6Base
  have he (j : Fin 6) : e6E j∈T := RootPairing.GeckConstruction.e_mem_lieAlgebra (E6Index j)
  fin_cases i
  · exact T.add_mem (he 0) (he 5)
  · exact T.add_mem (he 2) (he 4)
  · exact he 3
  · exact he 1

private theorem negative_mem_geck (i : Fin 4) :
    negative i∈RootPairing.GeckConstruction.lieAlgebra E6Base := by
  let T := RootPairing.GeckConstruction.lieAlgebra E6Base
  have hf (j : Fin 6) : e6F j∈T := RootPairing.GeckConstruction.f_mem_lieAlgebra (E6Index j)
  fin_cases i
  · exact T.add_mem (hf 0) (hf 5)
  · exact T.add_mem (hf 2) (hf 4)
  · exact hf 3
  · exact hf 1

theorem rational_image_mem_geck (x : RationalLie CartanMatrix.F₄) :
    rationalRepresentation x∈RootPairing.GeckConstruction.lieAlgebra E6Base := by
  let T := RootPairing.GeckConstruction.lieAlgebra E6Base
  let S := T.comap rationalRepresentation
  have hle : LieSubalgebra.lieSpan ℚ _ (Set.range (generator CartanMatrix.F₄))≤S := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨g,rfl⟩
    change rationalRepresentation (generator CartanMatrix.F₄ g)∈T
    cases g with
    | H i=>
      rw [rationalRepresentation_H]
      have he : ⁅positive i,negative i⁆=cartan i := by simpa only [if_pos rfl] using EF i i
      rw [←he]
      exact T.lie_mem (positive_mem_geck i) (negative_mem_geck i)
    | E i=>rw [rationalRepresentation_E];exact positive_mem_geck i
    | F i=>rw [rationalRepresentation_F];exact negative_mem_geck i
  rw [CFSGSerreLocalNilpotence.generator_lieSpan_eq_top] at hle
  exact hle (LieSubalgebra.mem_top x)

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
