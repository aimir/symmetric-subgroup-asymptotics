import SymmetricSubgroupAsymptotics.Non2PreE7CompleteCharacterIntervalSource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-!
# A uniform finite coefficient bound for complete character intervals

The correlated character-interval source has one finite automorphism
coefficient for every literal normal axis below its retained subgroup.  This
file bounds that whole coefficient from a single order ceiling for the
ambient finite group.  The argument is independent of the affine degree:
there are at most `2^(m^2)` normal axes and every quotient has at most
`2^(m^2)` automorphisms when the ambient group has order at most `2^m`.

This is the shared coefficient estimate used by the exceptional affine
component rows.  Their degree-specific work is therefore reduced to an
explicit order ceiling and the elementary inequality `2*m^2 <= 64*w`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

-- Keep the unfolded tail sum on the canonical subtype enumeration, as in
-- the source theorem which defines it.
attribute [-instance] originalNormalFintype

namespace CompleteCharacterIntervalData

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}

/-- A quotient of a finite group has no more elements than the group. -/
private theorem quotient_card_le_self (N : Subgroup U) [N.Normal] :
    Nat.card (U ⧸ N) ≤ Nat.card U :=
  Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

/-- An order ceiling `|U| <= 2^m` bounds the entire finite coefficient in a
complete character interval by `2^(2*m^2)`. -/
theorem tailConstant_le_two_pow_of_order
    (D : CompleteCharacterIntervalData U) (m : ℕ)
    (horder : Nat.card U ≤ 2 ^ m) :
    D.tailConstant ≤ ((2 ^ (m * m + m * m) : ℕ) : ℝ) := by
  let Ax := {N : {N : Subgroup U // N.Normal} // ¬ D.E ≤ N.1}
  have haxes : Nat.card Ax ≤ 2 ^ (m * m) := by
    apply (Nat.card_le_card_of_injective (fun N : Ax => N.1)
      (fun _ _ h => Subtype.ext h)).trans
    exact normalSubgroup_card_le_two_pow_sq m horder
  have hterm : ∀ N : Ax,
      (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) ≤
        ((2 ^ (m * m) : ℕ) : ℝ) := by
    intro N
    letI : N.1.1.Normal := N.1.2
    have hquot : Nat.card (U ⧸ N.1.1) ≤ 2 ^ m :=
      (quotient_card_le_self N.1.1).trans horder
    have haut : Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) ≤
        2 ^ (m * m) := by
      calc
        Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) ≤
            Nat.card (U ⧸ N.1.1) ^ Nat.log 2 (Nat.card (U ⧸ N.1.1)) :=
          Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log _
        _ ≤ (2 ^ m) ^ Nat.log 2 (Nat.card (U ⧸ N.1.1)) :=
          Nat.pow_le_pow_left hquot _
        _ ≤ (2 ^ m) ^ m := by
          apply Nat.pow_le_pow_right (by positivity)
          exact (Nat.log_mono_right (b := 2) hquot).trans_eq
            (Nat.log_pow (by norm_num) m)
        _ = 2 ^ (m * m) := by rw [pow_mul]
    exact_mod_cast haut
  change (∑ N : Ax,
      (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ)) ≤ _
  calc
    (∑ N : Ax,
        (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ)) ≤
        ∑ _N : Ax, ((2 ^ (m * m) : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun N _ => hterm N)
    _ = (Nat.card Ax : ℝ) * ((2 ^ (m * m) : ℕ) : ℝ) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ((2 ^ (m * m) : ℕ) : ℝ) * ((2 ^ (m * m) : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast haxes
      · positivity
    _ = ((2 ^ (m * m + m * m) : ℕ) : ℝ) := by
      norm_num [pow_add]

/-- Once `2*m^2` fits below `64*w`, the common logarithmic-square menu pays
the complete interval coefficient uniformly in the complement degree. -/
theorem tailConstant_le_menuMass_of_order
    (D : CompleteCharacterIntervalData U) (m : ℕ)
    (horder : Nat.card U ≤ 2 ^ m)
    (hw : 8 ≤ w) (hexp : m * m + m * m ≤ 64 * w) (b : ℕ) :
    D.tailConstant ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  calc
    D.tailConstant ≤ ((2 ^ (m * m + m * m) : ℕ) : ℝ) :=
      D.tailConstant_le_two_pow_of_order m horder
    _ = (2 : ℝ) ^ ((m * m + m * m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast hexp
    _ ≤ _ :=
      Non2UnipotentPrefixFiniteMenu.two_rpow_sixtyFour_width_le_menuMass hw b

end CompleteCharacterIntervalData

end SymmetricSubgroupAsymptotics

