import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead

/-! The genuine half-order ordinary cost on an original binary affine
block action. The bound follows from the already proved actual chief
trace and the literal translation/complement product. The actual top
rank remains explicit, with no permutation generator input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineOrderCost
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem component_card_le (hp : P.p = 2) :
    Nat.card block.Component ≤
      2^(translationDimension J block P + (translationDimension J block P)^2) := by
  let C := P.elementaryChart block.component_preprimitive
  let x : block.Fibre := ⟨x₀, block.map_base⟩
  have hv : Nat.card P.V = 2^translationDimension J block P := by
    calc
      Nat.card P.V = Nat.card block.Fibre := P.card_eq x
      _ = P.p^translationDimension J block P := fibre_card_eq_prime_pow_dimension J block P
      _ = _ := by rw [hp]
  have hh := P.complement_card_le_prime_pow_dimension_sq block.component_preprimitive C x
  rw [hp] at hh
  have hprod := (P.isComplement'_complement x).card_mul
  calc
    Nat.card block.Component = Nat.card P.V * Nat.card (P.complement x) := hprod.symm
    _ ≤ 2^translationDimension J block P * 2^((translationDimension J block P)^2) := by
      rw [hv]
      exact Nat.mul_le_mul_left _ hh
    _ = _ := (pow_add _ _ _).symm

theorem genRank_le_half_order_cost (hp : P.p = 2) (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      (((translationDimension J block P : ℝ)^2 + translationDimension J block P)/2) *
        Nat.card block.Points + MarkedC4.genRank block.Top := by
  have hl := OriginalBlockOrdinaryCompressionState.source_genRank_two_pow_le J block i
  have hc := component_card_le J block P hp
  have hu : Nat.card block.Component ^ Nat.card block.Points *
      2^(2*MarkedC4.genRank block.Top) ≤
      2^((translationDimension J block P + (translationDimension J block P)^2) *
        Nat.card block.Points + 2*MarkedC4.genRank block.Top) := by
    calc
      _ ≤ (2^(translationDimension J block P + (translationDimension J block P)^2)) ^
          Nat.card block.Points * 2^(2*MarkedC4.genRank block.Top) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc _)
      _ = _ := by rw [← pow_mul, ← pow_add]
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hl.trans hu)
  have heR : 2*(MarkedC4.genRank J : ℝ) ≤
      ((translationDimension J block P : ℝ) + (translationDimension J block P : ℝ)^2) *
        Nat.card block.Points + 2*MarkedC4.genRank block.Top := by exact_mod_cast he
  nlinarith

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineOrderCost
