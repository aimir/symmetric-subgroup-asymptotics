import SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryModelGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticLargeFieldModelGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryGenerationReduction

/-! The complete original C family has actual generating pairs. The
residual excludes the entire C tag while retaining every other previously
open concrete model obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration

theorem typeC_twoGenerated_of_index (r : ℕ) (q : CFSG.PrimePower)
    (hr : 2 ≤ r) (hsmall : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.C r q)] : TwoGenerated (CFSG.Models.C r q) := by
  by_cases hq2 : q.order = 2
  · exact typeC_binary_twoGenerated_of_index r q hr hsmall hq2
  · by_cases hq3 : q.order = 3
    · exact typeC_ternary_twoGenerated_rank r q hr hq3
    · have hq : 2 ≤ q.order := by
        change 2 ≤ q.prime ^ q.exponent
        have hh := Nat.one_lt_pow (Nat.ne_of_gt q.exponent_pos) q.prime_isPrime.one_lt
        omega
      exact typeC_large_field_twoGenerated r hr q (by omega)

def RemainingGenerationIndexWithoutTypeASuzukiC : CFSG.Index → Prop
  | .C _ _ _ _ => False
  | i => RemainingGenerationIndexWithoutTypeASuzukiBinaryC i

theorem model_twoGenerated_or_remaining_without_typeA_suzuki_C (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    TwoGenerated i.Model ∨ RemainingGenerationIndexWithoutTypeASuzukiC i := by
  cases i <;> try exact model_twoGenerated_or_remaining_without_typeA_suzuki_binaryC _ hn
  case C r q hr hs hsimple =>
    letI : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    exact Or.inl (typeC_twoGenerated_of_index r q hr hs)

theorem finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_C_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      IsCenterless i.Model → RemainingGenerationIndexWithoutTypeASuzukiC i →
        TwoGenerated i.Model) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCenterless G → TwoGenerated G := by
  apply finiteSimpleTwoGeneratorBound_of_cfsg_and_remaining_non_typeA_suzuki_binaryC_models hCFSG
  intro i _ _ hc _
  rcases model_twoGenerated_or_remaining_without_typeA_suzuki_C i
    (noncommutative_of_simple_centerless i.Model hc) with hgen | hremain
  · exact hgen
  · exact remaining i hc hremain

end SymmetricSubgroupAsymptotics.CFSGReduction
