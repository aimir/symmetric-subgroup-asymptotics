import SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

/-! Transport the bounded eight-point half-degree reduction through the
ACTUAL faithful action. The sporadic witness is a global minimal failed
action, not asserted to be a subquotient of this group. Full degree-three
S3 is not covered by the half-degree endpoint. No new finite-model bound
or current-degree induction premise occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
open EightPointHalfDegreeFiniteModelReduction

theorem counterexample_mono {b c : ℕ} (hbc : b ≤ c)
    (hbad : Nonempty (PrimitiveSporadicCounterexample b)) :
    Nonempty (PrimitiveSporadicCounterexample c) := by
  obtain ⟨w⟩ := hbad
  exact ⟨⟨w.degree,w.degree_ge_four,w.degree_le.trans hbc,w.group,
    w.transitive,w.primitive,w.failed,w.minimal,w.socle,w.sporadic,w.equiv⟩⟩

theorem two_mul_genRank_le_card_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) {G X : Type}
    [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 8) (hthree : Nat.card X ≠ 3) :
    2*MarkedC4.genRank G ≤ Nat.card X ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  let e : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  let rho : G →* Equiv.Perm (Fin (Nat.card X)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : G ≃* rho.range := MonoidHom.ofInjective hrho
  rcases EightPointHalfDegreeFiniteModelReduction.half_degree_or_sporadic_counterexample
    hCFSG (Nat.card X) hsmall rho.range (fun h => (hthree h).elim) with hpaid | hbad
  · exact Or.inl (by
      simpa only [← CoprimeNilpotentProductGenerators.genRank_mulEquiv f] using hpaid)
  · exact Or.inr (counterexample_mono hsmall hbad)

theorem exists_generating_finset_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) {G X : Type}
    [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 8) (hthree : Nat.card X ≠ 3) :
    (∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ 2*S.card ≤ Nat.card X) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases two_mul_genRank_le_card_or_sporadic_counterexample hCFSG (G := G) (X := X) hsmall hthree with hpaid | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
    exact Or.inl ⟨S,hgen,by rw [hcard]; exact hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
