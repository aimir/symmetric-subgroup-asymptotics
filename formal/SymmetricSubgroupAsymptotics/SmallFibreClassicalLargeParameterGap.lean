import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGModelComponentIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleIndexBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare

/-! The literal B/C/D/twisted-D parameter tails pay the original
binary/ternary subnormal class gap. Each root-star index and original
least-index-square is combined with the same proved logarithmic-or-power
order packet. Only the complementary smaller parameter range is retained;
the original source, top, subgroup and both degree forms are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreClassicalLargeParameterGap
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

theorem subnormal_gap_or_typeB_small_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : E.Simple ≃* CFSG.Models.B r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order^(r-1) < 2048 := by
  by_cases hlarge : 2048 ≤ q.order^(r-1)
  · left
    letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.B r q) := Finite.of_equiv E.Simple e.toEquiv
    apply of_model π hπ c hc hsize E e ?_ ?_ ?_ H hH
    · intro K hK
      exact hlarge.trans
        (CFSGOrthogonalBOriginalMatrixBounds.typeB_field_power_le_proper_index r hr q K hK)
    · intro K hK
      exact Or.inl
        (CFSGOrthogonalBProperIndexOrderBudget.typeB_order_mul_outer_le_proper_index_log_power
          r hr q K hK)
    · intro ell hell
      exact (typeB_simpleIndexBounds r hr q ell hell).1
  · exact Or.inr (by omega)

theorem subnormal_gap_or_typeC_small_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    (e : E.Simple ≃* CFSG.Models.C r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order^(r-1) < 2048 := by
  by_cases hlarge : 2048 ≤ q.order^(r-1)
  · left
    letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.C r q) := Finite.of_equiv E.Simple e.toEquiv
    apply of_model π hπ c hc hsize E e ?_ ?_
      (typeC_leastProperIndex_square_lt_card r q hr hsmall) H hH
    · intro K hK
      exact hlarge.trans (typeC_field_power_le_proper_index r hr q K hK)
    · intro K hK
      exact Or.inl
        (CFSGSymplecticProperIndexOrderBudget.typeC_order_mul_outer_le_proper_index_log_power
          r hr q K hK)
  · exact Or.inr (by omega)

theorem subnormal_gap_or_typeD_small_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : E.Simple ≃* CFSG.Models.D r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order^(r-1) < 2048 := by
  by_cases hlarge : 2048 ≤ q.order^(r-1)
  · left
    letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.D r q) := Finite.of_equiv E.Simple e.toEquiv
    apply of_model π hπ c hc hsize E e ?_ ?_
      (typeD_leastProperIndex_square_lt_card r q hr) H hH
    · intro K hK
      exact hlarge.trans
        (CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index r hr q K hK)
    · intro K hK
      exact Or.inl
        (CFSGOrthogonalDProperIndexOrderBudget.typeD_order_mul_outer_le_proper_index_log_power
          r hr q K hK)
  · exact Or.inr (by omega)

theorem subnormal_gap_or_twistedD_small_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : E.Simple ≃* CFSG.Models.TwistedD r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ q.order^(r-2) < 2048 := by
  by_cases hlarge : 2048 ≤ q.order^(r-2)
  · left
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.TwistedD r q) := Finite.of_equiv E.Simple e.toEquiv
    have hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
      fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
    apply of_model π hπ c hc hsize E e ?_ ?_
      (typeTwistedD_leastProperIndex_square_lt_card r q hr) H hH
    · intro K hK
      exact hlarge.trans
        (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index r hr q K hK)
    · intro K hK
      by_cases hfour : r=4
      · subst r
        exact Or.inr
          ((CFSGTwistedDProperIndexOrderBudget.typeTwistedD_four_order_mul_outer_le_proper_index_power
            q hn K hK).trans (Nat.pow_le_pow_right
              (lt_trans Nat.zero_lt_one (K.one_lt_index_of_ne_top hK)) (by decide : 34 ≤ 66)))
      · exact Or.inl
          (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_high_order_mul_outer_le_proper_index_log_power
            r (by omega) q hn K hK)
  · exact Or.inr (by omega)

end SymmetricSubgroupAsymptotics.SmallFibreClassicalLargeParameterGap
