import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Whole split-D and minus-D small-fibre consumers on the original
nonaffine data. The only retained head is literal minus D4 over F2.
The same subnormal subgroup, all socle factors and both degree forms
are handled by the checked scaled-packet consumer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreOrthogonalDClassGap
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

theorem subnormal_class_cube_gap_of_typeD
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : E.Simple ≃* CFSG.Models.D r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D r q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.D r q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  exact of_model π hπ c hc hsize E e
    (CFSGOrthogonalDScaledClassPacket.typeD_scaled_class_cube_le_proper_index r hr q hn)
    (typeD_leastProperIndex_square_lt_card r q hr) H hH

theorem subnormal_gap_or_twistedD_binary_rank_four
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : E.Simple ≃* CFSG.Models.TwistedD r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ (r=4 ∧ q.order=2) := by
  by_cases hhead : r=4 ∧ q.order=2
  · exact Or.inr hhead
  · apply Or.inl
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.TwistedD r q) := Finite.of_equiv E.Simple e.toEquiv
    have hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
      fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
    exact of_model π hπ c hc hsize E e
      (CFSGOrthogonalDScaledClassPacket.typeTwistedD_scaled_class_cube_le_proper_index
        r hr q hn hhead)
      (typeTwistedD_leastProperIndex_square_lt_card r q hr) H hH

end SymmetricSubgroupAsymptotics.SmallFibreOrthogonalDClassGap
