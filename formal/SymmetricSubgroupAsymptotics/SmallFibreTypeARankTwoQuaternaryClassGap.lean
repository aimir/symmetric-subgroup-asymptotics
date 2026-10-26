import SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoQuaternaryClassPacket
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original rank-two quaternary model pays the24-reserve on the
SAME original small-fibre action, all actual socle factors and both
primitive degree forms. Only the actual marking is supplied; the class,
outer, proper-index and least-index-square packets are proved inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoQuaternaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem of_model {S : Type} [Group S] [Finite S]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X) (e : E.Simple ≃* S)
    (hscaled : ∀ K : Subgroup S, K ≠ ⊤ →
      24*(Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 3^K.index)
    (hsquare : ∀ ell : ℕ, LeastProperIndex S ell → ell^2 < Nat.card S)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses S) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  apply SmallFibreTwentyFourClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
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

theorem subnormal_class_cube_gap_of_typeA_rank_two_order_four
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : q.order=4)
    (e : E.Simple ≃* CFSG.Models.A 2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 2 q) := Finite.of_equiv E.Simple e.toEquiv
  exact of_model π hπ c hc hsize E e
    (CFSGTypeARankTwoQuaternaryClassPacket.scaled_class_cube_le_proper_index q hq)
    (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card 2 (by decide) q) H hH

end SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoQuaternaryClassGap
