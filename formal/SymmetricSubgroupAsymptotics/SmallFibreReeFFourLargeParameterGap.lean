import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.ReeFFourScaledClassEnvelopeNumerics
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiIndex
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual positive-parameter ReeF4 top pays the binary/ternary
small-fibre class gap from m=3. This retains the original top, every
subnormal source, all socle factors, and the full factorial. The positive
parameters m=1,2 and the separate Tits model are not covered here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeFFourLargeParameterGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_reeFFour_large_parameter
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 3 ≤ m) (e : E.Simple ≃* CFSG.Models.ReeF4 m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 m) := Finite.of_equiv E.Simple e.toEquiv
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hindex := CFSGReeFFourMiddleSuzukiIndex.middle_suzuki_le_proper_index
      m (by omega) (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hindex
    have horder : Nat.card E.Simple*Nat.card (Outer E.Simple) ≤
        ReeFFourOrderCubeTailNumerics.fieldOrder m^26*(2*m+1) := by
      rw [Nat.card_congr e.toEquiv,outer_card_congr e]
      exact Nat.mul_le_mul
        (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le m)
        (CFSGReeFFourOriginalOuterBound.outer_card_le m (by omega))
    have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    calc
      25*(Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤
          25*(ReeFFourOrderCubeTailNumerics.fieldOrder m^26*(2*m+1))^3 :=
        Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left
          ((Nat.mul_le_mul_right _ hclass).trans horder) 3)
      _ ≤ 3^ReeFFourMiddleSuzukiClassNumerics.indexBound m :=
        ReeFFourScaledClassEnvelopeNumerics.scaled_component_cube m hm
      _ ≤ 3^K.index := Nat.pow_le_pow_right (by decide) hindex
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGReeFFourOriginalIndexSquare.original_index_square m (by omega) ell
      (leastProperIndex_of_mulEquiv e ell hell)

end SymmetricSubgroupAsymptotics.SmallFibreReeFFourLargeParameterGap
