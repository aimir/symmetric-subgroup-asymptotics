import SymmetricSubgroupAsymptotics.LargeTopSmallFibreClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.PrimitiveSocleIndexOrderBudget

/-! Three structural sources of the SAME actual top-order budget in a
binary or ternary original block action. Affine profiles and both raw
socle degree forms retain their original top group and point set. The
index-form component order/outer budget remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LargeTopSmallFibreStructureBounds
open OriginalBlockClassBound PrimitiveSocleRawStructure

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem cube_of_top_order (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (horder : Nat.card (Top (A := A) (X := X)) ≤
      Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 24)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  rcases hc with rfl | rfl
  · exact LargeTopSmallFibreClassBound.binary_class_cube_le b hb hsize hn horder
  · exact LargeTopSmallFibreClassBound.ternary_class_cube_le b hb hsize hn horder

theorem class_cube_le_of_affine_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (P : PrimitiveAffineProfile (Top (A := A) (X := X)) X) (x₀ : X) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  apply cube_of_top_order b hb c hc hsize hn
  calc
    Nat.card (Top (A := A) (X := X)) ≤
        Nat.card X * Nat.card X ^ Nat.log 2 (Nat.card X) :=
      P.card_le_domain_pow_log x₀
    _ = Nat.card X ^ (Nat.log 2 (Nat.card X) + 1) := by
      rw [pow_succ,Nat.mul_comm]
    _ ≤ Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 24) :=
      Nat.pow_le_pow_right (by omega) (by omega)

theorem class_cube_le_of_power_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (a : ℕ) (hka : D.factorCount ≤ 2 * a)
    (hdegree : Nat.card X = (Nat.card D.Simple) ^ a) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  apply cube_of_top_order b hb c hc hsize hn
  exact (D.card_le_degree_pow_log_of_power_form a hka hdegree (by omega)).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem class_cube_le_of_index_top (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = c)
    (hn : 4096 ≤ Nat.card X)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (hcomponent : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤
      K.index ^ (4 * Nat.log 2 K.index + 23)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) :=
  cube_of_top_order b hb c hc hsize hn
    (D.card_le_log_order_of_index_form K hK hdegree hcomponent)

end SymmetricSubgroupAsymptotics.LargeTopSmallFibreStructureBounds
