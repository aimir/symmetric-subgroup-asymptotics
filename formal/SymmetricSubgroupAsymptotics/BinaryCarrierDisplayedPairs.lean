import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk000
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk001
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk002
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk003
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk004
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk005
import SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairsChunk006

/-! The complete 41-by-41 literal displayed scalar table, with the
original physical masses, colors and two mark coefficients. The pair
proof assembles separately checked row declarations. This does not
identify or count any actual group, normal subgroup, owner or weight. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs

open BinaryCarrierCone BinaryCarrierStarEnvelope

private theorem vec_six_zero {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (0 : Fin 6) = a := rfl

private theorem vec_six_one {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (1 : Fin 6) = b := rfl

private theorem vec_six_two {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (2 : Fin 6) = c := rfl

private theorem vec_six_three {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (3 : Fin 6) = d := rfl

private theorem vec_six_four {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (4 : Fin 6) = e := rfl

private theorem vec_six_five {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem displayed_head_le (i : Fin 41) :
    ((displayedRows i).k : ℝ) ≤ (4 * displayedScale i) * alpha (displayedColor i) := by
  fin_cases i <;>
    norm_num [displayedRows, displayedScale, displayedColor, alpha,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem displayed_second_le (i : Fin 41) :
    ((max (displayedRows i).m (displayedRows i).a₂ : ℕ) : ℝ) ≤
      (4 * displayedScale i) * beta (displayedColor i) := by
  fin_cases i <;>
    norm_num [displayedRows, displayedScale, displayedColor, beta,
      vec_six_zero, vec_six_one, vec_six_two, vec_six_three, vec_six_four, vec_six_five]

theorem displayed_pair_le (i j : Fin 41) :
    (displayedRows i).symmetricSupport (displayedRows j) ≤
      (4 * displayedScale i) * (4 * displayedScale j) *
        pairMatrix64 (displayedColor i) (displayedColor j) / 64 := by
  fin_cases i
  · exact row00_le j
  · exact BinaryCarrierDisplayedPairTable.displayed_row_one_pair_le j
  · exact row02_le j
  · exact row03_le j
  · exact row04_le j
  · exact row05_le j
  · exact row06_le j
  · exact row07_le j
  · exact row08_le j
  · exact row09_le j
  · exact row10_le j
  · exact row11_le j
  · exact row12_le j
  · exact row13_le j
  · exact row14_le j
  · exact row15_le j
  · exact row16_le j
  · exact row17_le j
  · exact row18_le j
  · exact row19_le j
  · exact row20_le j
  · exact row21_le j
  · exact row22_le j
  · exact row23_le j
  · exact row24_le j
  · exact row25_le j
  · exact row26_le j
  · exact row27_le j
  · exact row28_le j
  · exact row29_le j
  · exact row30_le j
  · exact row31_le j
  · exact row32_le j
  · exact row33_le j
  · exact row34_le j
  · exact row35_le j
  · exact row36_le j
  · exact row37_le j
  · exact row38_le j
  · exact row39_le j
  · exact row40_le j

end SymmetricSubgroupAsymptotics.BinaryCarrierDisplayedPairs
