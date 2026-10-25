import SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual

/-! Exhaust the literal classifier for the remaining bounded nonaffine
component. All proved component profiles are excluded, so its SAME
simple factor is Tits or sporadic. This does not assert a class bound
for those remaining models or for the separate small-fibre branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual
open PrimitiveSocleRawStructure

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem bounded_component_has_finite_factor (h : BoundedNonaffineComponent D) :
    ∃ E : NonaffineData D.Component D.Fibre, ∃ i : CFSG.Index,
      (i = .tits ∨ ∃ s : CFSG.Sporadic, i = .sporadic s) ∧
      Nonempty (E.Simple ≃* i.Model) ∧
      ((∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Fibre = K.index ^ E.factorCount) ∨
        (∃ a : ℕ, E.factorCount ≤ 2 * a ∧ Nat.card D.Fibre = (Nat.card E.Simple) ^ a)) := by
  obtain ⟨_, _, _, E, i, ⟨e⟩, hform, _, _, hg, hE, hA, hAlt, hU, hC, hB, hD, hEx⟩ := h
  refine ⟨E, i, ?_, ⟨e⟩, hform⟩
  cases i with
  | cyclic p hp =>
      have hc : IsMulCommutative (Multiplicative (ZMod p)) := inferInstance
      exact (E.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)).elim
  | alternating n hn => exact (hAlt ⟨n, hn, ⟨e⟩⟩).elim
  | A r q hr hs => exact (hA ⟨r, q, hr, hs, ⟨e⟩⟩).elim
  | B r q hr => exact (hB ⟨r, q, hr, ⟨e⟩⟩).elim
  | C r q hr hs => exact (hC ⟨r, q, hr, hs, ⟨e⟩⟩).elim
  | D r q hr => exact (hD ⟨r, q, hr, Or.inl ⟨e⟩⟩).elim
  | E6 q => exact (hE (Or.inl ⟨q, ⟨e⟩⟩)).elim
  | E7 q => exact (hE (Or.inr (Or.inl ⟨q, ⟨e⟩⟩))).elim
  | E8 q => exact (hE (Or.inr (Or.inr ⟨q, ⟨e⟩⟩))).elim
  | F4 q => exact (hEx (Or.inl ⟨q, ⟨e⟩⟩)).elim
  | G2 q hs => exact (hg ⟨q, hs, rfl⟩).elim
  | twistedA r q hr hs => exact (hU ⟨r, q, hr, hs, ⟨e⟩⟩).elim
  | twistedD r q hr => exact (hD ⟨r, q, hr, Or.inr ⟨e⟩⟩).elim
  | twistedE6 q => exact (hEx (Or.inr (Or.inl ⟨q, ⟨e⟩⟩))).elim
  | trialityD4 q => exact (hEx (Or.inr (Or.inr (Or.inl ⟨q, ⟨e⟩⟩)))).elim
  | suzuki m hm =>
      exact (hEx (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩))))).elim
  | reeG2 m hm =>
      exact (hEx (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩)))))).elim
  | reeF4 m hm =>
      exact (hEx (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, by omega, ⟨e⟩⟩)))))).elim
  | tits => exact Or.inl rfl
  | sporadic s => exact Or.inr ⟨s, rfl⟩

end SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual
