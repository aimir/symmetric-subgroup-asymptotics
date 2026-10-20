import SymmetricSubgroupAsymptotics.SixPairFiveCycleWordB6Witness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairSourceCatalogue
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! A primitive-six word certificate on a transitive original action gives
an actual representative-facing B6 source. The single point conjugacy moves
the physical frame and the retained words together; no normal registry or
new source estimate is required. This constructs one source, not coverage
of the complete 182-class catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleActualRepresentativeSource
open Non2UnipotentPrefixFiniteMenu

variable {n : ℕ} {generators : Fin n → Equiv.Perm (Fin 12)}
  (W : SixPairFiveCycleWordB6Witness generators)

private theorem word_top (w : List (Fin n)) :
    W.frame.top (W.evalWord w) = (w.map W.tops).prod := by
  have hg (i : Fin n) : W.frame.top (closureGenerators generators i) = W.tops i :=
    BinaryPairFrame.ofGenerators_top_generator _ _ _ W.preserves i
  induction w with
  | nil => exact map_one W.frame.top
  | cons i w ih =>
    change W.frame.top (closureGenerators generators i * W.evalWord w) = _
    rw [map_mul, hg, ih]
    rfl

/-- The same word certificate on the actual point-conjugate group. -/
def relabelActionCertificate (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (c : Equiv.Perm (Fin 12)) :
    PreE7B6ActionCertificate (relabelSubgroup c
      (Subgroup.closure (Set.range generators))) := by
  let e := BinaryPairFrame.sourceRelabelEquiv
    (U := Subgroup.closure (Set.range generators)) c
  exact SixPairFiveCycleAllNormalB6.actionCertificate (W.frame.relabelPoints c) h6 hZmud
    (e (W.evalWord W.fiveCycleWord)) (e (W.evalWord W.moverWord)) W.mover
    ((W.frame.relabelPoints_top_sourceRelabelEquiv c _).trans
      ((word_top W _).trans W.fiveCycle_eval))
    ((W.frame.relabelPoints_top_sourceRelabelEquiv c _).trans
      ((word_top W _).trans W.mover_eval)) W.moves W.matrix

private theorem not_binary_of_transitive
    (H : Subgroup (Equiv.Perm (Fin 12)))
    (htrans : MulAction.IsPretransitive H (Fin 12)) : ¬ IsPGroup 2 H := by
  letI := htrans
  intro h
  obtain ⟨d, hd⟩ := h.card_orbit (0 : Fin 12)
  have hc : Nat.card (MulAction.orbit H (0 : Fin 12)) = 12 := by
    rw [MulAction.orbit_eq_univ]
    exact (Nat.card_congr (Equiv.Set.univ (Fin 12))).trans (Nat.card_fin 12)
  rw [hc] at hd
  by_cases hsmall : d < 4
  · interval_cases d <;> norm_num at hd
  · have hbig : (16 : ℕ) ≤ 2 ^ d :=
      pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by omega : 4 ≤ d)
    omega

include W in
/-- Actual action-class membership, correspondence and source are produced
together. Transitivity is on the literal original twelve points. -/
theorem exists_actualRepresentativeSource
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (htrans : MulAction.IsPretransitive
      (Subgroup.closure (Set.range generators)) (Fin 12)) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c (Subgroup.closure (Set.range generators)) = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) := by
  let H := Subgroup.closure (Set.range generators)
  obtain ⟨i, c, hc⟩ := Non2TransitiveActionClass.representative_cover H
    (not_binary_of_transitive H htrans) htrans
  have hr : relabelSubgroup c H = i.representative := by
    have he : relabelSubgroup c H = MulAut.conj c • H := by
      change H.map c.permCongrHom.toMonoidHom = _
      rw [Subgroup.pointwise_smul_def]
      congr 1
    exact he.trans hc
  have hpre : IsPreE7ActionClass 12 i := by
    intro d hd
    have hg := d.pairCount_ge_24
    change 2 * d.pairCount = 12 at hd
    omega
  have hframe : Nonempty (BinaryPairFrame i.representative (Fin 6)) := by
    rw [← hr]
    exact ⟨W.frame.relabelPoints c⟩
  let p : PreE7PairActionClass 6 := ⟨⟨i, hpre⟩, hframe⟩
  refine ⟨p, c, hr, ⟨?_⟩⟩
  change PreE7B6ActionCertificate i.representative
  rw [← hr]
  exact relabelActionCertificate W h6 hZmud c

end SymmetricSubgroupAsymptotics.SixPairFiveCycleActualRepresentativeSource
end
