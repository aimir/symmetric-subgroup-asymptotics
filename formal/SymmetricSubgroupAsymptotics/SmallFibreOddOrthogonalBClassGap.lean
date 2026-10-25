import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSimpleIndexBounds
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every odd-characteristic original B model of rank at least three
pays the original small-fibre class gap, retaining the SAME E, H,
all socle factors and both actual degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreOddOrthogonalBClassGap
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

theorem subnormal_class_cube_gap_of_odd_typeB
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hodd : q.prime ≠ 2)
    (e : E.Simple ≃* CFSG.Models.B r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.B r q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.B r q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  exact of_model π hπ c hc hsize E e
    (CFSGOrthogonalBOddScaledClassPacket.typeB_scaled_class_cube_le_proper_index r hr q hodd hn)
    (fun ell hell => (typeB_simpleIndexBounds r hr q ell hell).1) H hH

end SymmetricSubgroupAsymptotics.SmallFibreOddOrthogonalBClassGap
