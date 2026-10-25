import SymmetricSubgroupAsymptotics.SmallFibreGTwoClassGap
import SymmetricSubgroupAsymptotics.CFSGGTwoPuncturedScalarClassPacket

/-! Every original admissible G2 top pays the SAME binary/ternary
subnormal class gap. Field four uses its genuine punctured-annihilator
index64; the previously proved packet pays all other fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreGTwoCompleteClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_gTwo
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hs : q.order ≠ 2) (e : E.Simple ≃* CFSG.Models.G2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  rcases SmallFibreGTwoClassGap.subnormal_gap_or_gTwo_field_four
    π hπ c hc hsize E q hs e H hH with hgap | hfour
  · exact hgap
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.G2 q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.G2 q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses (CFSG.Models.G2 q)) := by
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
    have hh := CFSGGTwoPuncturedScalarClassPacket.field_four_scaled_class_cube_le_proper_index
      q hfour hn (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hh
    rw [hclasses,outer_card_congr e]
    exact hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGGTwoOriginalIndexSquare.typeGTwo_index_square q hs ell
      (leastProperIndex_of_mulEquiv e ell hell)

end SymmetricSubgroupAsymptotics.SmallFibreGTwoCompleteClassGap
