import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.SmallReeScaledClassEnvelopeNumerics
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOrderBounds
import SymmetricSubgroupAsymptotics.CFSGReeGTwoRectangularPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The whole original small-Ree family pays the original binary/ternary
subnormal class gap. The literal rectangular index 3q and the same model's
order-times-outer ceiling q^8 supply the scaled packet at every actual
proper subgroup. All socle factors and both degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeGTwoClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_reeGTwo
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 1 ≤ m) (e : E.Simple ≃* CFSG.Models.ReeG2 m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeG2 m) := Finite.of_equiv E.Simple e.toEquiv
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hindex := CFSGReeGTwoRectangularPermutationDegree.three_field_card_le_proper_index
      m hm (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hindex
    have horder : Nat.card E.Simple*Nat.card (Outer E.Simple) ≤ (3^(2*m+1))^8 := by
      rw [Nat.card_congr e.toEquiv,outer_card_congr e]
      exact CFSGReeGTwoOriginalOrderBounds.original_component_le_eighth m hm
    have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    calc
      25*(Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤
          25*((3^(2*m+1))^8)^3 :=
        Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left
          ((Nat.mul_le_mul_right _ hclass).trans horder) 3)
      _ ≤ 3^(3*3^(2*m+1)) :=
        SmallReeScaledClassEnvelopeNumerics.scaled_component_cube (2*m+1) (by omega)
      _ ≤ 3^K.index := Nat.pow_le_pow_right (by decide) hindex
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGReeGTwoOriginalIndexSquare.original_index_square m hm ell
      (leastProperIndex_of_mulEquiv e ell hell)

end SymmetricSubgroupAsymptotics.SmallFibreReeGTwoClassGap
