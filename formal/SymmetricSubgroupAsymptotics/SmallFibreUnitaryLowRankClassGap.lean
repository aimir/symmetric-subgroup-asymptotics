import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGUnitaryLowRankScaledTail
import SymmetricSubgroupAsymptotics.CFSGUnitaryAdmissibleIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual low-rank unitary field tails retain the original source,
actual subnormal H, every socle factor and both degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreUnitaryLowRankClassGap
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

theorem subnormal_class_cube_gap_of_unitary_low_rank_tail
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (q : CFSG.PrimePower)
    (hwindow : (r=2 ∧ 11 ≤ q.order) ∨ (r=3 ∧ 5 ≤ q.order))
    (e : E.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  have hr : 2 ≤ r := by rcases hwindow with h | h <;> omega
  have hsmall : r=2 → q.order≠2 := by rcases hwindow with h | h <;> omega
  exact of_model π hπ c hc hsize E e
    (CFSGUnitaryLowRankScaledTail.scaled_class_cube_le_proper_index r q hwindow hn)
    (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_leastIndex_square_lt r hr q hsmall) H hH

end SymmetricSubgroupAsymptotics.SmallFibreUnitaryLowRankClassGap
