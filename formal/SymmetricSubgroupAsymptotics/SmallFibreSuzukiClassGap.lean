import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.SuzukiScaledClassEnvelopeNumerics
import SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusIndex
import SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality
import SymmetricSubgroupAsymptotics.CFSGSuzukiOuterBound
import SymmetricSubgroupAsymptotics.CFSGSuzukiLeastIndexOrder
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The whole original Suzuki family pays the same binary/ternary
subnormal class gap. Its first field uses the actual class equation at
the quadratic/torus index; its remaining parameters use one scaled
order tail. The actual top, source subgroup and all socle factors remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreSuzukiClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction
open SuzukiQuadraticTorusClassNumerics

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_suzuki
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 1 ≤ m) (e : E.Simple ≃* CFSG.Models.Suzuki m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.Suzuki m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.Suzuki m) := Finite.of_equiv E.Simple e.toEquiv
  have hN : Nat.card E.Simple=orderBound (fieldOrder m) := by
    rw [Nat.card_congr e.toEquiv,CFSGSuzukiModelCardinality.model_card,
      CFSGSuzukiFieldParameters.field_card]
    rfl
  have hO : Nat.card (Outer E.Simple) ≤ 2*m+1 := by
    rw [outer_card_congr e]
    exact CFSGSuzukiOuterBound.outer_card_le m hm
  have hindex : ∀ K : Subgroup E.Simple, K ≠ ⊤ → indexBound m ≤ K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := CFSGSuzukiQuadraticTorusIndex.suzuki_quadratic_torus_le_proper_index
      m hm (K.map e.toMonoidHom) hmap
    change indexBound m ≤ (K.map e.toMonoidHom).index at hh
    exact hh.trans_eq (K.index_map_equiv e)
  have hscaled : 25*(Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤
      3^(indexBound m) := by
    by_cases hone : m=1
    · subst m
      have hz : Subgroup.center E.Simple=⊥ := by
        rcases (inferInstance : (Subgroup.center E.Simple).Normal).eq_bot_or_eq_top with h | h
        · exact h
        · exact (E.noncommutative (Subgroup.center_eq_top_iff.mp h)).elim
      have hclass := CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
        (indexBound 1) (by decide) hz hindex
      rw [hN] at hclass
      have hhead : orderBound (fieldOrder 1)/indexBound 1+1=1041 := by decide
      rw [hhead] at hclass
      have hout : Nat.card (Outer E.Simple) ≤ 3 := hO
      exact (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left
        (Nat.mul_le_mul hclass hout) 3)).trans (by decide +kernel)
    · have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
        Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
      have hh := Nat.mul_le_mul hclass hO
      rw [hN] at hh
      exact (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hh 3)).trans
        (SuzukiScaledClassEnvelopeNumerics.scaled_component_cube_tail m (by omega))
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    exact hscaled.trans (Nat.pow_le_pow_right (by decide) (hindex K hK))
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGSuzukiLeastIndexOrder.leastProperIndex_square_lt_card m hm ell
      (leastProperIndex_of_mulEquiv e ell hell)

end SymmetricSubgroupAsymptotics.SmallFibreSuzukiClassGap
