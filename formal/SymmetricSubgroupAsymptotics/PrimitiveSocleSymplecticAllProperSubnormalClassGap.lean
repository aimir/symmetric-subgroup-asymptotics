import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticOrderProperClassPackets
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticSmallProperClassPackets
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticBinaryProperClassPackets

/-! Every admissible original C model pays the proper-subnormal extra
exponent. The exact same coupled/primary packets retain all factors,
the original subnormal subgroup and both actual degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem binary_order_eq_four (q : CFSG.PrimePower) (hp : q.prime=2)
    (hne : q.order≠2) (hsmall : ¬8 ≤ q.order) : q.order=4 := by
  have he : q.exponent ≤ 2 := by
    by_contra hh
    apply hsmall
    change 8 ≤ q.prime^q.exponent
    rw [hp]
    exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 3 ≤ q.exponent)
  have hexp : q.exponent=1 ∨ q.exponent=2 := by have := q.exponent_pos; omega
  rcases hexp with h | h
  · exact (hne (by change q.prime^q.exponent=2; rw [hp,h,pow_one])).elim
  · change q.prime^q.exponent=4
    norm_num [hp,h]

private theorem binary_order_eq_two (q : CFSG.PrimePower) (hp : q.prime=2)
    (hsmall : ¬4 ≤ q.order) : q.order=2 := by
  have he : q.exponent=1 := by
    by_contra hh
    have htwo : 2 ≤ q.exponent := by have := q.exponent_pos; omega
    apply hsmall
    change 4 ≤ q.prime^q.exponent
    rw [hp]
    exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) htwo
  change q.prime^q.exponent=2
  rw [hp,he,pow_one]

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.C r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hr2 : r=2
  · subst r
    by_cases hp : q.prime=2
    · by_cases hlarge : 8 ≤ q.order
      · exact D.proper_subnormal_class_cube_le_of_typeC_rank_two_order_capacity
          q (Or.inr ⟨hp,hlarge⟩) e H hH hne
      · exact D.proper_subnormal_class_cube_le_of_typeC_four_rank_two
          q (binary_order_eq_four q hp (hsmall rfl) hlarge) e H hH hne
    · by_cases hlarge : 7 ≤ q.order
      · exact D.proper_subnormal_class_cube_le_of_typeC_rank_two_order_capacity
          q (Or.inl ⟨hp,hlarge⟩) e H hH hne
      · have hp3 : 3 ≤ q.prime := by have h := q.prime_isPrime.two_le; omega
        have he : q.exponent=1 := by
          by_contra hne
          have he2 : 2 ≤ q.exponent := by have h := q.exponent_pos; omega
          have h9 : 9 ≤ q.order :=
            (Nat.pow_le_pow_left hp3 2).trans
              (Nat.pow_le_pow_right (by omega : 0<q.prime) he2)
          omega
        have horder : q.order=q.prime := by change q.prime^q.exponent=q.prime; rw [he,pow_one]
        have hfields : q.order=3 ∨ q.order=5 := by
          obtain ⟨k,hk⟩ := q.prime_isPrime.odd_of_ne_two hp
          omega
        exact D.proper_subnormal_class_cube_le_of_typeC_small_odd_prime q hfields e H hH hne
  have hr3 : 3 ≤ r := by omega
  by_cases hp : q.prime=2
  · by_cases hwindow : 4 ≤ q.order ∨ 5 ≤ r
    · exact D.proper_subnormal_class_cube_le_of_typeC_binary_higher_rank
        r hr3 q hp e hwindow H hH hne
    · have hq2 := binary_order_eq_two q hp (fun h => hwindow (Or.inl h))
      have hrank : r=3 ∨ r=4 := by omega
      rcases hrank with rfl | rfl
      · exact D.proper_subnormal_class_cube_le_of_typeC_binary_rank_three q hq2 e H hH hne
      · exact D.proper_subnormal_class_cube_le_of_typeC_binary_point_rank_four q hq2 e H hH hne
  · exact D.proper_subnormal_class_cube_le_of_typeC_odd_higher_rank r hr3 q hp e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
