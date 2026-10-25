import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGModelComponentIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGPSLTwoLeastIndexOrder
import SymmetricSubgroupAsymptotics.CFSGUnitaryAdmissibleIndexSquare

/-! Whole higher-A, rank-one A and unitary parameter tails in the SAME
actual small-fibre action. Their proved field/rank proper-index bounds
and actual logarithmic order packets pay the scaled class envelope.
The alternatives retain only literal smaller field/rank parameters,
not a supplied bounded-degree class estimate or an action catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreTypeAUnitaryLargeParameterGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction
open CFSGModelComponentIndexOrderBudget

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem of_model {S : Type} [Group S]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X) (e : E.Simple ≃* S)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → 2048 ≤ K.index)
    (horder : ComponentIndexOrderBudget S)
    (hsquare : ∀ ell : ℕ, LeastProperIndex S ell → ell^2 < Nat.card S)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_log_or_power_order
    π hπ c hc hsize E ?_ (budget_of_mulEquiv e horder) ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    have hh := hindex (K.map e.toMonoidHom) hmap
    rw [hi] at hh
    exact hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact hsquare ell (leastProperIndex_of_mulEquiv e ell hell)

theorem subnormal_gap_or_higherA_small_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (e : E.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order^r < 2048 := by
  by_cases hlarge : 2048 ≤ q.order^r
  · left
    letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
    apply of_model π hπ c hc hsize E e ?_ ?_
      (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hr q) H hH
    · intro K hK
      exact hlarge.trans
        (CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hr q K hK)
    · intro K hK
      exact Or.inl
        (CFSGTypeAProperIndexOrderBudget.typeA_order_mul_outer_le_proper_index_log_power
          r (by omega) q K hK)
  · exact Or.inr (by omega)

theorem subnormal_gap_or_pslTwo_small_field
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : 4 ≤ q.order)
    (e : E.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order < 4096 := by
  by_cases hlarge : 4096 ≤ q.order
  · left
    letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
    apply of_model π hπ c hc hsize E e ?_ ?_ ?_ H hH
    · intro K hK
      have hh : q.order ≤ 2*K.index := by
        simpa only [q.card_field] using
          CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F := q.Field) K hK
      omega
    · intro K hK
      exact Or.inl
        (CFSGTypeAProperIndexOrderBudget.typeA_order_mul_outer_le_proper_index_log_power
          1 (by decide) q K hK)
    · intro ell hell
      exact CFSGPSLTwoGeometry.leastProperIndex_square_lt_card
        (F := q.Field) (by simpa only [q.card_field] using hq) ell hell
  · exact Or.inr (by omega)

theorem subnormal_gap_or_unitary_small_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    (e : E.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order^r < 2048 := by
  by_cases hlarge : 2048 ≤ q.order^r
  · left
    letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv E.Simple e.toEquiv
    have hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
      fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
    apply of_model π hπ c hc hsize E e ?_ ?_
      (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_leastIndex_square_lt r hr q hsmall) H hH
    · intro K hK
      exact hlarge.trans
        (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_field_power_le_proper_index
          r hr q hsmall K hK)
    · intro K hK
      left
      exact (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_mul_outer_le_proper_index_log_power
        r hr q hsmall hn K hK).trans
          (Nat.pow_le_pow_right (lt_trans Nat.zero_lt_one (K.one_lt_index_of_ne_top hK))
            (by omega : 4*Nat.log 2 K.index+3 ≤ 4*Nat.log 2 K.index+23))
  · exact Or.inr (by omega)

end SymmetricSubgroupAsymptotics.SmallFibreTypeAUnitaryLargeParameterGap
