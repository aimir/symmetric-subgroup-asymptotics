import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.HeisenbergScaledClassEnvelopeNumerics
import SymmetricSubgroupAsymptotics.NonabelianSimpleClassOrderHalf
import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryQuadraticLeviIndex
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddlePairingIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRegularModuleIndex
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual Heisenberg and binary indices pay the scaled class
packet for every original F4 and triality model. The proved coarse
component bounds q^66 and q^35 are retained. Binary triality uses the
generic class-equation half-order saving with its actual outer order.
Every socle factor, original subnormal subgroup and degree form remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreFFourTrialityClassGap
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

private theorem three_le_prime_of_order_eq_three (q : CFSG.PrimePower) (hq : q.order=3) :
    3 ≤ q.prime := by
  have hp : q.prime=3 :=
    (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_three q.exponent_pos.ne'
      (by decide : (1:ℕ) ≠ 0)
      (show q.prime^q.exponent=3^1 by simpa only [pow_one] using hq)).1
  omega

theorem subnormal_class_cube_gap_of_fFour
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.F4 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.F4 q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.F4 q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  apply of_model π hπ c hc hsize E e ?_
    (CFSGFFourE6OriginalIndexSquare.original_index_square q.Field q.prime) H hH
  intro K hK
  have hclass : Nat.card (ConjClasses (CFSG.Models.F4 q)) ≤ Nat.card (CFSG.Models.F4 q) :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hcomponent := (Nat.mul_le_mul_right (Nat.card (Outer (CFSG.Models.F4 q))) hclass).trans
    (CFSGFFourOriginalOrderUpper.typeFFour_order_mul_outer_le q hn)
  have hcube := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)
  by_cases hq : 3 ≤ q.order
  · exact (hcube.trans
      (HeisenbergScaledClassEnvelopeNumerics.scaled_order_cube q.order q.prime hq
        q.prime_isPrime.two_le (three_le_prime_of_order_eq_three q))).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGFFourE6HeisenbergIndex.typeFFour_heisenberg_le_proper_index q K hK))
  · have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    have hq2 : q.order=2 := by omega
    rw [hq2] at hcube
    exact (hcube.trans (by decide +kernel : 25*((2:ℕ)^66)^3 ≤ 3^128)).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGFFourBinaryQuadraticLeviIndex.typeFFour_binary_levi_le_proper_index q hq2 K hK))

theorem subnormal_class_cube_gap_of_triality
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.TrialityD4 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TrialityD4 q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.TrialityD4 q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  apply of_model π hπ c hc hsize E e ?_
    (CFSGTrialityGeckOriginalIndexSquare.original_index_square q) H hH
  intro K hK
  by_cases hq : 3 ≤ q.order
  · have hclass : Nat.card (ConjClasses (CFSG.Models.TrialityD4 q)) ≤
        Nat.card (CFSG.Models.TrialityD4 q) :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    have hcomponent : Nat.card (CFSG.Models.TrialityD4 q)*
        Nat.card (Outer (CFSG.Models.TrialityD4 q)) ≤ q.order^35 :=
      (Nat.mul_le_mul (CFSGTrialityGeckOriginalOrderUpper.original_order_le_power q hn)
        (CFSGTrialityGeckProperIndexOrderBudget.original_outer_card_le_power q)).trans_eq (by ring)
    have hclass66 := ((Nat.mul_le_mul_right _ hclass).trans hcomponent).trans
      (Nat.pow_le_pow_right (by omega : 0 < q.order) (by decide : 35 ≤ 66))
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hclass66 3)).trans
      (HeisenbergScaledClassEnvelopeNumerics.scaled_order_cube q.order q.prime hq
        q.prime_isPrime.two_le (three_le_prime_of_order_eq_three q))).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGTrialityGeckMiddlePairingIndex.typeTriality_middle_le_proper_index q K hK))
  · have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    have hq2 : q.order=2 := by omega
    have he : q.exponent=1 :=
      (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
        (by decide : (1:ℕ) ≠ 0)
        (show q.prime^q.exponent=2^1 by simpa only [pow_one] using hq2)).2
    have horder : Nat.card (CFSG.Models.TrialityD4 q) ≤ 12*2^28 := by
      simpa only [hq2] using
        CFSGTrialityGeckOriginalOrderUpper.original_order_le_twelve_mul_power q hn
    have hhalf := NonabelianSimpleClassOrderHalf.twice_class_card_le_order hn
    have hclass : Nat.card (ConjClasses (CFSG.Models.TrialityD4 q)) ≤ 6*2^28 := by omega
    have hout : Nat.card (Outer (CFSG.Models.TrialityD4 q)) ≤ 3 := by
      simpa only [he,mul_one] using
        CFSGTrialityGeckOriginalOuterBound.original_outer_card_le_three_exponent q
    have hcomponent := (Nat.mul_le_mul hclass hout).trans_eq
      (by ring : (6*2^28)*3=18*2^28)
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)).trans
      (by decide +kernel : 25*(18*(2:ℕ)^28)^3 ≤ 3^64)).trans
      (Nat.pow_le_pow_right (by decide)
        (CFSGTrialityBinaryRegularModuleIndex.typeTriality_binary_regular_le_proper_index q hq2 K hK))

end SymmetricSubgroupAsymptotics.SmallFibreFFourTrialityClassGap
