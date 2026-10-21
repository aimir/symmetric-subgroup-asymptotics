import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import Mathlib.Data.Nat.Log

/-! Polylogarithmic counting of the possible literal soluble complements
in a fixed affine translation group. This counts subgroups of its actual
automorphism group, without classifying those subgroups or using matrices. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers

def logSize (n : ℕ) : ℕ := Nat.log2 n + 1

theorem card_le_two_pow_logSize (n : ℕ) : n ≤ 2 ^ logSize n := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  exact h.le.trans_eq (by rw [logSize, Nat.log2_eq_log_two])

theorem automorphism_card_le_two_pow_logSize_sq (T : Type*) [Group T] [Finite T] :
    Nat.card (MulAut T) ≤ 2 ^ (logSize (Nat.card T) * logSize (Nat.card T)) := by
  have haut := Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log T
  rw [← Nat.log2_eq_log_two] at haut
  calc
    Nat.card (MulAut T) ≤ Nat.card T ^ Nat.log2 (Nat.card T) := haut
    _ ≤ (2 ^ logSize (Nat.card T)) ^ Nat.log2 (Nat.card T) :=
      Nat.pow_le_pow_left (card_le_two_pow_logSize (Nat.card T)) _
    _ ≤ (2 ^ logSize (Nat.card T)) ^ logSize (Nat.card T) :=
      Nat.pow_le_pow_right (by positivity) (by unfold logSize; omega)
    _ = _ := by rw [pow_mul]

def SolubleComplement (T : Type*) [Group T] :=
  {H : Subgroup (MulAut T) // IsSolvable H}

instance finiteSolubleComplement (T : Type*) [Group T] [Finite T] :
    Finite (SolubleComplement T) := by
  letI solublePrimitiveCount_finiteAut : Finite (MulAut T) :=
    Finite.of_injective (fun e : MulAut T => (e : T → T)) DFunLike.coe_injective
  exact Subtype.finite

theorem solubleComplement_card_le (T : Type*) [Group T] [Finite T] :
    Nat.card (SolubleComplement T) ≤ 2 ^ (logSize (Nat.card T) ^ 4) := by
  letI solublePrimitiveCount_finiteAut : Finite (MulAut T) :=
    Finite.of_injective (fun e : MulAut T => (e : T → T)) DFunLike.coe_injective
  have hsub := subgroup_card_le_two_pow_sq
    (logSize (Nat.card T) * logSize (Nat.card T))
    (automorphism_card_le_two_pow_logSize_sq T)
  calc
    Nat.card (SolubleComplement T) ≤ Nat.card (Subgroup (MulAut T)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ ≤ 2 ^ ((logSize (Nat.card T) * logSize (Nat.card T)) *
        (logSize (Nat.card T) * logSize (Nat.card T))) := hsub
    _ = _ := by congr 1; ring

end SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers
