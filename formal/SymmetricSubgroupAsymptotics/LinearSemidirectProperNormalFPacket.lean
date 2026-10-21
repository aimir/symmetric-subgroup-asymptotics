import SymmetricSubgroupAsymptotics.LinearSemidirectProperNormalFCentralizer
import SymmetricSubgroupAsymptotics.NormalFMixedCommutatorQuotientBounds

/-! One actual proper normal subgroup pays both factors through the same
original translation-axis denominator. The centralizer may be larger than
the centre of the quotient, so it is bounded directly. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
open SemidirectProduct MarkedC4.RDTNormalFInterface
variable {p : ℕ} [Fact p.Prime] {R V : Type}
    [Group R] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Finite R] [Finite V]
    (rho : R →* (V ≃ₗ[ZMod p] V))

theorem properNormalF_unit_packet
    (B C A : Submodule (ZMod p) V) (z : R)
    (hCB : C ≤ B) (hAC : A ≤ C)
    (hz : z ∈ Subgroup.center R)
    (hC : ∀ r v, v ∈ C → rho r v ∈ C)
    (hBdisp : ∀ r v, v ∈ B → rho r v - v ∈ C)
    (hzdisp : ∀ v, rho z v - v ∈ C)
    (hCcard : Nat.card C ≤ 16 * Nat.card A)
    (hcenter : Nat.card {v : V // rho z v - v ∈ A} *
      Nat.card {t : R // ∀ v, v ∈ B → rho t v - v ∈ A} ≤ 16 * Nat.card A)
    (N : Subgroup (Model rho)) [N.Normal]
    (hNA : ∀ v, (inl (Multiplicative.ofAdd v) : Model rho) ∈ N ↔ v ∈ A) :
    ∃ W : Subgroup (Model rho ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  letI : Finite (Model rho) :=
    Finite.of_equiv (Multiplicative V × R) SemidirectProduct.equivProd.symm
  let F := properNormalF rho B z
  letI : F.Normal := properNormalF_normal rho B C z hCB hz hC hBdisp hzdisp
  let W := F.map (QuotientGroup.mk' N)
  letI : W.Normal := Subgroup.Normal.map inferInstance (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hAN : translationSpace rho A ≤ N := by
    intro g hg
    have he : g = (inl g.left : Model rho) := by
      apply SemidirectProduct.ext
      · rfl
      · exact hg.1
    rw [he]
    exact (hNA g.left.toAdd).mpr hg.2
  have hAc : Nat.card A ≤ Nat.card N := by
    rw [← translationSpace_card rho A]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hAN)
      (Subgroup.inclusion_injective hAN)
  have hcomm : Nat.card (targetCommutator W) ≤ 2 ^ 4 := by
    apply targetCommutator_quotient_card_le N F (translationSpace rho C)
      (translationSpace rho A)
      (properNormalF_mixedCommutator_le rho B C z hz hC hBdisp hzdisp)
    · intro g hg
      exact ⟨hg.1, hAC hg.2⟩
    · exact hAN
    · simpa only [translationSpace_card] using hCcard
  have hcentermul := (properNormalF_quotient_centralizer_card_mul_le rho B A z hz N hNA).trans hcenter
  have hcentral : Nat.card (targetCentralizer W) ≤ 2 ^ 4 := by
    change Nat.card (Subgroup.centralizer (W : Set (Model rho ⧸ N))) ≤ _
    have hp := Nat.card_pos (α := N)
    have hm : Nat.card N * Nat.card (Subgroup.centralizer (W : Set (Model rho ⧸ N))) ≤
        Nat.card N * 16 := hcentermul.trans (by nlinarith)
    exact Nat.le_of_mul_le_mul_left hm hp
  refine ⟨W, inferInstance, ?_⟩
  exact normalF_unit_packet_of_actual_card_bounds W 4 4 8 4 hcomm hcentral (by decide) le_rfl

end SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
