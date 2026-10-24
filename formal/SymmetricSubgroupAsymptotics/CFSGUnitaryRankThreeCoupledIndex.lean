import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeCoupledStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergModelIndex

/-! The literal normalizer extension maps to the SAME original simple
rank-three unitary group. A genuine surviving central root moves a coset
of each proper subgroup; its pulled-back stabilizer supplies the coupled
binary24 or ternary48 bound. No faithful extension embedding is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

private theorem normalizer_degree_of_central_motion
    (q : CFSG.PrimePower) (b : ℕ)
    (hindex : ∀ M : Subgroup (rankThreeNormalizerExtension q),
      ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl → b ≤ M.index)
    {X : Type*} [Finite X] [MulAction (rankThreeNormalizerExtension q) X]
    (x : X) (a : Multiplicative (centralParameters q 1))
    (hx : (SemidirectProduct.inl (centralRadicalHom q 1 a) :
      rankThreeNormalizerExtension q) • x ≠ x) : b ≤ Nat.card X := by
  let M := MulAction.stabilizer (rankThreeNormalizerExtension q) x
  have hM : ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl := by
    intro he
    have ha : centralRadicalHom q 1 a ∈ M.comap SemidirectProduct.inl := he ⟨a, rfl⟩
    exact hx ha
  have hm : M.index ≤ Nat.card X := by
    calc
      _ = Nat.card (MulAction.orbit (rankThreeNormalizerExtension q) x) :=
        (Nat.card_congr
          (MulAction.orbitEquivQuotientStabilizer (rankThreeNormalizerExtension q) x)).symm
      _ ≤ Nat.card X := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (hindex M hM).trans hm

private def rankThreeProjectiveExtensionHom (q : CFSG.PrimePower) :
    rankThreeNormalizerExtension q →* CFSG.Models.TwistedA 3 q :=
  (unitaryProjectiveCover q 0).comp (unitaryRadicalNormalizerExtensionHom q 1)

private theorem rankThreeProjectiveExtensionHom_central (q : CFSG.PrimePower)
    (a : Multiplicative (centralParameters q 1)) :
    rankThreeProjectiveExtensionHom q (SemidirectProduct.inl (centralRadicalHom q 1 a)) =
      projectiveCentralParameterHom q 0 a := by
  change unitaryProjectiveCover q 0 (unitaryRadicalNormalizerExtensionHom q 1
    (SemidirectProduct.inl (centralRadicalHom q 1 a))) = _
  rw [unitaryRadicalNormalizerExtensionHom_inl]
  rfl

private theorem normalizer_index_of_central_survival
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (q : CFSG.PrimePower) (b : ℕ)
    (hindex : ∀ M : Subgroup (rankThreeNormalizerExtension q),
      ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl → b ≤ M.index)
    (F : rankThreeNormalizerExtension q →* G)
    (a : Multiplicative (centralParameters q 1))
    (ha : F (SemidirectProduct.inl (centralRadicalHom q 1 a)) ≠ 1)
    (H : Subgroup G) (hH : H ≠ ⊤) : b ≤ H.index := by
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ ha
  letI : MulAction (rankThreeNormalizerExtension q) (G ⧸ H) := MulAction.compHom _ F
  have hb := normalizer_degree_of_central_motion q b hindex x a hx
  simpa only [Subgroup.index_eq_card] using hb

private theorem rankThree_original_coupled_index
    (q : CFSG.PrimePower) (b : ℕ)
    (hindex : ∀ M : Subgroup (rankThreeNormalizerExtension q),
      ¬ (centralRadicalHom q 1).range ≤ M.comap SemidirectProduct.inl → b ≤ M.index)
    [IsSimpleGroup (CFSG.Models.TwistedA 3 q)]
    (H : Subgroup (CFSG.Models.TwistedA 3 q)) (hH : H ≠ ⊤) : b ≤ H.index := by
  letI : Finite (CFSG.Models.TwistedA 3 q) := twistedA_shifted_finite q 0
  obtain ⟨c, _, hc⟩ := exists_radicalCentre_projective_ne_one q 0
  let a := (centralRadicalKernelEquiv q 1).symm c
  have ha : centralRadicalKernelEquiv q 1 a = c :=
    (centralRadicalKernelEquiv q 1).apply_symm_apply c
  have hn : rankThreeProjectiveExtensionHom q
      (SemidirectProduct.inl (centralRadicalHom q 1 a)) ≠ 1 := by
    rw [rankThreeProjectiveExtensionHom_central]
    rw [← projectiveRadicalCentreHom_equiv_apply, ha]
    exact hc
  exact normalizer_index_of_central_survival q b hindex
    (rankThreeProjectiveExtensionHom q) a hn H hH

theorem twistedA_rankThree_binary_coupled_proper_index
    (q : CFSG.PrimePower) (hq : q.order = 2)
    [IsSimpleGroup (CFSG.Models.TwistedA 3 q)]
    (H : Subgroup (CFSG.Models.TwistedA 3 q)) (hH : H ≠ ⊤) : 24 ≤ H.index :=
  rankThree_original_coupled_index q 24 (rankThree_binary_semidirect_coupled_index q hq) H hH

theorem twistedA_rankThree_ternary_coupled_proper_index
    (q : CFSG.PrimePower) (hq : q.order = 3)
    [IsSimpleGroup (CFSG.Models.TwistedA 3 q)]
    (H : Subgroup (CFSG.Models.TwistedA 3 q)) (hH : H ≠ ⊤) : 48 ≤ H.index :=
  rankThree_original_coupled_index q 48 (rankThree_ternary_semidirect_coupled_index q hq) H hH

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
