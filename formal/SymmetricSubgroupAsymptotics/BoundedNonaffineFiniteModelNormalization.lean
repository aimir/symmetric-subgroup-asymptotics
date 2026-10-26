import SymmetricSubgroupAsymptotics.OriginalMinimalBlockNonaffineShapeResidual

/-! Normalize the already selected model of the bounded nonaffine
component residual. Every excluded constructor is contradicted by its
actual equivalence profile; the original E, model index, and both degree
forms are retained. No classification call, model recognition, or new
class budget is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BoundedNonaffineFiniteModelNormalization
open PrimitiveSocleRawStructure OriginalMinimalBlockNonaffineShapeResidual CFSGReduction

theorem index_is_tits_or_sporadic
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (E : NonaffineData G X) (i : CFSG.Index) (e : E.Simple ≃* i.Model)
    (hG2 : ¬ ∃ (q : CFSG.PrimePower) (hs : q.order≠2),i=.G2 q hs)
    (hE : ¬ ((∃ q : CFSG.PrimePower,Nonempty (E.Simple ≃* CFSG.Models.E6 q)) ∨
      (∃ q : CFSG.PrimePower,Nonempty (E.Simple ≃* CFSG.Models.E7 q)) ∨
      (∃ q : CFSG.PrimePower,Nonempty (E.Simple ≃* CFSG.Models.E8 q))))
    (hA : ¬ TypeAProfile E.Simple)
    (hAlt : ¬ ∃ m : ℕ,5 ≤ m ∧ Nonempty (E.Simple ≃* alternatingGroup (Fin m)))
    (hU : ¬ UnitaryProfile E.Simple) (hC : ¬ SymplecticProfile E.Simple)
    (hB : ¬ TypeBProfile E.Simple) (hD : ¬ OrthogonalDProfile E.Simple)
    (hEx : ¬ PrimitiveSocleExceptionalProperClassProfile.Profile E.Simple) :
    i=.tits ∨ ∃ s : CFSG.Sporadic,i=.sporadic s := by
  cases i with
  | cyclic p hp =>
    have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
      change IsMulCommutative (Multiplicative (ZMod p))
      infer_instance
    exact (E.noncommutative ((isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm => exact (hAlt ⟨m,hm,⟨e⟩⟩).elim
  | A r q hr hs => exact (hA ⟨r,q,hr,hs,⟨e⟩⟩).elim
  | B r q hr => exact (hB ⟨r,q,hr,⟨e⟩⟩).elim
  | C r q hr hs => exact (hC ⟨r,q,hr,hs,⟨e⟩⟩).elim
  | D r q hr => exact (hD ⟨r,q,hr,Or.inl ⟨e⟩⟩).elim
  | E6 q => exact (hE (Or.inl ⟨q,⟨e⟩⟩)).elim
  | E7 q => exact (hE (Or.inr (Or.inl ⟨q,⟨e⟩⟩))).elim
  | E8 q => exact (hE (Or.inr (Or.inr ⟨q,⟨e⟩⟩))).elim
  | F4 q => exact (hEx (Or.inl ⟨q,⟨e⟩⟩)).elim
  | G2 q hs => exact (hG2 ⟨q,hs,rfl⟩).elim
  | twistedA r q hr hs => exact (hU ⟨r,q,hr,hs,⟨e⟩⟩).elim
  | twistedD r q hr => exact (hD ⟨r,q,hr,Or.inr ⟨e⟩⟩).elim
  | twistedE6 q => exact (hEx (Or.inr (Or.inl ⟨q,⟨e⟩⟩))).elim
  | trialityD4 q => exact (hEx (Or.inr (Or.inr (Or.inl ⟨q,⟨e⟩⟩)))).elim
  | suzuki m hm =>
    exact (hEx (Or.inr (Or.inr (Or.inr (Or.inl ⟨m,hm,⟨e⟩⟩))))).elim
  | reeG2 m hm =>
    exact (hEx (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m,hm,⟨e⟩⟩)))))).elim
  | reeF4 m hm =>
    exact (hEx (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m,by omega,⟨e⟩⟩)))))).elim
  | tits => exact Or.inl rfl
  | sporadic s => exact Or.inr ⟨s,rfl⟩

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem actual_finite_model_of_bounded_component (h : BoundedNonaffineComponent D) :
    (Nat.card D.Points=2 ∨ Nat.card D.Points=3) ∧
    5≤Nat.card D.Fibre ∧ Nat.card D.Fibre≤4095 ∧
    ∃ E : NonaffineData D.Component D.Fibre,∃ i : CFSG.Index,
      (i=.tits ∨ ∃ s : CFSG.Sporadic,i=.sporadic s) ∧ Nonempty (E.Simple ≃* i.Model) ∧
      ((∃ K : Subgroup E.Simple,K≠⊤ ∧ Nat.card D.Fibre=K.index^E.factorCount) ∨
        (∃ a : ℕ,E.factorCount≤2*a ∧ Nat.card D.Fibre=(Nat.card E.Simple)^a)) ∧
      ¬ IsSimpleGroup D.Component ∧
      (¬ ∃ m : ℕ,5 ≤ m ∧ Nonempty (D.Component ≃* Equiv.Perm (Fin m))) := by
  obtain ⟨hblocks,hlo,hhi,E,i,⟨e⟩,hform,hsimple,hsym,hG2,hE,hA,hAlt,hU,hC,hB,hD,hEx⟩ := h
  exact ⟨hblocks,hlo,hhi,E,i,
    index_is_tits_or_sporadic E i e hG2 hE hA hAlt hU hC hB hD hEx,
    ⟨e⟩,hform,hsimple,hsym⟩

end SymmetricSubgroupAsymptotics.BoundedNonaffineFiniteModelNormalization
