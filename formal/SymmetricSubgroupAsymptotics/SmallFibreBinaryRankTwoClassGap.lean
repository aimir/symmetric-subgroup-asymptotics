import SymmetricSubgroupAsymptotics.SmallFibreCharTwoClassicalClassGap
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoScaledTail
import SymmetricSubgroupAsymptotics.CFSGSymplecticFieldFourPuncturedClassPacket

/-! The four-element-field puncture and uniform q>=8 tail fill every
admissible characteristic-two rank-two C model. Together with the
literal higher-rank packet only binary rank three remains. The original
subnormal H and E, all factors and both degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreBinaryRankTwoClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem of_model {S : Type} [Group S] [Finite S]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X) (e : E.Simple ≃* S)
    (hscaled : ∀ K : Subgroup S, K ≠ ⊤ →
      25*(Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 3^K.index)
    (hsquare : ∀ ell : ℕ, LeastProperIndex S ell → ell^2 < Nat.card S)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses S) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := hscaled (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hh
    rw [hclasses,outer_card_congr e]
    exact hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact hsquare ell (leastProperIndex_of_mulEquiv e ell hell)

theorem subnormal_class_cube_gap_of_charTwo_rankTwo
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hp : q.prime=2) (hq : q.order ≠ 2)
    (e : E.Simple ≃* CFSG.Models.C 2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.C 2 q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.C 2 q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  apply of_model π hπ c hc hsize E e ?_
    (typeC_leastProperIndex_square_lt_card 2 q (by decide) (by intro _; exact hq)) H hH
  intro K hK
  by_cases hlarge : 8 ≤ q.order
  · exact CFSGSymplecticBinaryRankTwoScaledTail.scaled_class_cube_le_proper_index
      q hp hlarge hn K hK
  · have hf : q.exponent ≤ 2 := by
      by_contra hh
      have hthree : 3 ≤ q.exponent := by omega
      have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hthree
      have hqpow : q.order=2^q.exponent := by change q.prime^q.exponent=_; rw [hp]
      rw [←hqpow] at hpow
      exact hlarge hpow
    have hf2 : q.exponent=2 := by
      have hfpos := q.exponent_pos
      by_contra hh
      have hf1 : q.exponent=1 := by omega
      apply hq
      change q.prime^q.exponent=2
      rw [hp,hf1,pow_one]
    have hq4 : q.order=4 := by
      change q.prime^q.exponent=4
      rw [hp,hf2]
      decide
    exact CFSGSymplecticFieldFourPuncturedClassPacket.scaled_class_cube_le_proper_index q hq4 K hK

theorem subnormal_gap_or_charTwo_typeC_binary_rank_three
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hp : q.prime=2)
    (hsmall : r=2 → q.order ≠ 2) (e : E.Simple ≃* CFSG.Models.C r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ (r=3 ∧ q.order=2) := by
  by_cases hr3 : 3 ≤ r
  · exact SmallFibreCharTwoClassicalClassGap.subnormal_gap_or_charTwo_typeC_binary_rank_three
      π hπ c hc hsize E r hr3 q hp e H hH
  · have hr2 : r=2 := by omega
    subst r
    exact Or.inl (subnormal_class_cube_gap_of_charTwo_rankTwo
      π hπ c hc hsize E q hp (hsmall rfl) e H hH)

end SymmetricSubgroupAsymptotics.SmallFibreBinaryRankTwoClassGap
