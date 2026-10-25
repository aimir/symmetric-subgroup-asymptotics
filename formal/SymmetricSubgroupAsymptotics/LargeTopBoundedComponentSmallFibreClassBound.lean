import SymmetricSubgroupAsymptotics.LargePrimitiveWideSmallFibreClassNumerics
import SymmetricSubgroupAsymptotics.LargeTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! A bounded order/outer budget for the actual simple component gives
an order budget for the SAME top, uniformly in its factor count. This
pays the actual binary/ternary block action above4096 blocks. No full
product kernel, primitive class callback or new simple model is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.card_le_degree_pow_bounded_component
    (D : NonaffineData G X) (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (hcomponent : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66) :
    Nat.card G ≤ Nat.card X ^ (66 + Nat.log 2 (Nat.card X)) := by
  let m := K.index
  let k := D.factorCount
  have hm : 2 ≤ m := K.one_lt_index_of_ne_top hK
  have hpow : 2 ^ k ≤ m ^ k := Nat.pow_le_pow_left hm k
  have hklog : k ≤ Nat.log 2 (m ^ k) := Nat.le_log_of_pow_le (by decide) hpow
  have hkn : k ≤ m ^ k := k.lt_two_pow_self.le.trans hpow
  have hfac : k.factorial ≤ (m ^ k) ^ k :=
    (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hkn k)
  have he : (m ^ 66) ^ k = (m ^ k) ^ 66 := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    Nat.card G ≤ (m ^ 66) ^ k * k.factorial :=
      D.card_le_simple_outer_wreath.trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcomponent k))
    _ ≤ (m ^ 66) ^ k * (m ^ k) ^ k := Nat.mul_le_mul_left _ hfac
    _ = (m ^ k) ^ (66 + k) := by rw [he,← pow_add]
    _ ≤ (m ^ k) ^ (66 + Nat.log 2 (m ^ k)) :=
      Nat.pow_le_pow_right (pow_pos (by omega) _) (by omega)
    _ = Nat.card X ^ (66 + Nat.log 2 (Nat.card X)) := by rw [← hdegree]

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

namespace SymmetricSubgroupAsymptotics.LargeTopBoundedComponentSmallFibreClassBound
open OriginalBlockClassBound SmallPermutationClassBudgets PrimitiveSocleRawStructure

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem cube_of_wide_top_order (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (horder : Nat.card (Top (A := A) (X := X)) ≤
      Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 30)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Fintype X := Fintype.ofFinite _
  have hbudget : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => subgroup_class_card_le_three (hsize x).le L
  have hrec := PermutationBlockClassReduction.class_card_le_product_mul_top b hb
    (fun _ => c) hbudget
  have hrec' : Nat.card (ConjClasses A) ≤ c ^ Nat.card X *
      Nat.card (ConjClasses (Top (A := A) (X := X))) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hrec
  have ht : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤
      Nat.card (Top (A := A) (X := X)) :=
    Nat.card_le_card_of_surjective (@ConjClasses.mk (Top (A := A) (X := X)) _)
      ConjClasses.mk_surjective
  have hbound := hrec'.trans (Nat.mul_le_mul_left _ ht)
  have hnum : (c ^ Nat.card X * Nat.card (Top (A := A) (X := X))) ^ 3 ≤
      5 ^ (c * Nat.card X - 1) := by
    rcases hc with rfl | rfl
    · exact LargePrimitiveWideSmallFibreClassNumerics.binary_product_cube_le _ _ hn horder
    · exact LargePrimitiveWideSmallFibreClassNumerics.ternary_product_cube_le _ _ hn horder
  have hfinal := (Nat.pow_le_pow_left hbound 3).trans hnum
  have he := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b c hsize
  simpa only [he,Nat.mul_comm (Nat.card X) c] using hfinal

theorem class_cube_le_of_bounded_component_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (hcomponent : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  apply cube_of_wide_top_order b hb c hc hsize hn
  have hlog : 12 ≤ Nat.log 2 (Nat.card X) :=
    Nat.le_log_of_pow_le (by decide)
      (show 2 ^ 12 ≤ Nat.card X by simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using hn)
  exact (D.card_le_degree_pow_bounded_component K hK hdegree hcomponent).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

end SymmetricSubgroupAsymptotics.LargeTopBoundedComponentSmallFibreClassBound
