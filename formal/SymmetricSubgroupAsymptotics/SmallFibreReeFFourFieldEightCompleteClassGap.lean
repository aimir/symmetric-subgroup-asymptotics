import SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightSingleIndexResidual
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSylowIndexObstruction

/-! The actual Sylow congruence eliminates the last SAME-K index109
residual. This supplies the full original q8 small-fibre class gap for
both fibre sizes and every socle factor count, preserving the original
source subgroup and its actual subnormal image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightCompleteClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

theorem proper_index_twoEighteen_le [IsSimpleGroup (CFSG.Models.ReeF4 1)]
    (K : Subgroup (CFSG.Models.ReeF4 1)) (hK : K≠⊤) : 218≤K.index := by
  rcases SmallFibreReeFFourFieldEightSingleIndexResidual.proper_index_eq_oneOhNine_or_large
      K hK with he|hlarge
  · exact (CFSGReeFFourFieldEightSylowIndexObstruction.index_ne_oneOhNine K he).elim
  · exact hlarge

theorem subnormal_class_cube_gap
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple ≃* CFSG.Models.ReeF4 1)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  rcases SmallFibreReeFFourFieldEightSingleIndexResidual.subnormal_gap_or_same_index_oneOhNine
      π hπ c hc hsize E e H hH with hgap|⟨_,K,_,_,hindex⟩
  · exact hgap
  · have heq : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    exact (CFSGReeFFourFieldEightSylowIndexObstruction.index_ne_oneOhNine
      (K.map e.toMonoidHom) (heq.trans hindex)).elim

end SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightCompleteClassGap
