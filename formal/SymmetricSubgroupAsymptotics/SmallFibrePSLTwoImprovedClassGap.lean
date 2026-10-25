import SymmetricSubgroupAsymptotics.SmallFibrePSLTwoClassGap
import SymmetricSubgroupAsymptotics.CFSGPSLTwoImprovedScaledClassPacket

/-! The improved PSL2 parameter packet closes the SAME original
small-fibre action, its actual arbitrary subnormal H, all socle factors,
and the existing actual degree forms. The tiny six-field frontier is
not replaced by the stronger, possibly false scaled inequality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibrePSLTwoImprovedClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_pslTwo
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hprofile : CFSGPSLTwoImprovedScaledClassPacket.FieldProfile q)
    (e : E.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 1 q) := Finite.of_equiv E.Simple e.toEquiv
  have hq : 4≤q.order := by
    rcases hprofile with ⟨_,hq⟩ | ⟨_,hq⟩ | hq | hq <;> omega
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses (CFSG.Models.A 1 q)) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := CFSGPSLTwoImprovedScaledClassPacket.scaled_class_cube_le_proper_index q hprofile
      (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hh
    rw [hclasses,outer_card_congr e]
    exact hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGPSLTwoGeometry.leastProperIndex_square_lt_card (F:=q.Field)
      (by rw [q.card_field]; exact hq) ell (leastProperIndex_of_mulEquiv e ell hell)

end SymmetricSubgroupAsymptotics.SmallFibrePSLTwoImprovedClassGap
