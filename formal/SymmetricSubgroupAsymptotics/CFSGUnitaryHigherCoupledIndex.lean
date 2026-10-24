import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergModelIndex

/-! A surviving actual central root element moves a coset of every
proper subgroup of the original simple unitary model. The SAME pulled
back middle-extension stabilizer gives the coupled lower bound. The
middle special-unitary vector dimension is at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

theorem higherUnitary_coupled_degree_of_central_motion (q : CFSG.PrimePower) (s : ℕ)
    {X : Type*} [Finite X] [MulAction (higherUnitaryPointParabolic q s) X]
    (x : X) (c : Multiplicative (centralParameters q (s + 2)))
    (hx : (SemidirectProduct.inl (centralRadicalHom q (s + 2) c) :
      higherUnitaryPointParabolic q s) • x ≠ x) :
    q.prime * ((q.order ^ 2 - 1) * q.order ^ (2 * s + 3)) ≤ Nat.card X := by
  let M := MulAction.stabilizer (higherUnitaryPointParabolic q s) x
  have hM : ¬ (centralRadicalHom q (s + 2)).range ≤ M.comap SemidirectProduct.inl := by
    intro he
    have hc : centralRadicalHom q (s + 2) c ∈ M.comap SemidirectProduct.inl := he ⟨c, rfl⟩
    exact hx hc
  have hindex : M.index ≤ Nat.card X := by
    calc
      _ = Nat.card (MulAction.orbit (higherUnitaryPointParabolic q s) x) :=
        (Nat.card_congr
          (MulAction.orbitEquivQuotientStabilizer (higherUnitaryPointParabolic q s) x)).symm
      _ ≤ Nat.card X := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (higherUnitary_semidirect_coupled_index q s M hM).trans hindex

private theorem higherExtension_central_apply (q : CFSG.PrimePower) (s : ℕ)
    (a : Multiplicative (centralParameters q (s + 2))) :
    higherUnitaryProjectiveExtensionHom q s
        (SemidirectProduct.inl (centralRadicalHom q (s + 2) a)) =
      projectiveCentralParameterHom q (s + 1) a := by
  rw [higherUnitaryProjectiveExtensionHom_inl]
  rfl

private theorem higherCoupledIndex_of_central_survival
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (q : CFSG.PrimePower) (s : ℕ) (F : higherUnitaryPointParabolic q s →* G)
    (a : Multiplicative (centralParameters q (s + 2)))
    (ha : F (SemidirectProduct.inl (centralRadicalHom q (s + 2) a)) ≠ 1)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    q.prime * ((q.order ^ 2 - 1) * q.order ^ (2 * s + 3)) ≤ H.index := by
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ ha
  letI : MulAction (higherUnitaryPointParabolic q s) (G ⧸ H) := MulAction.compHom _ F
  have hb := higherUnitary_coupled_degree_of_central_motion q s x a hx
  simpa only [Subgroup.index_eq_card] using hb

theorem twistedA_shifted_higher_coupled_proper_index (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 4) q)]
    (H : Subgroup (CFSG.Models.TwistedA (s + 4) q)) (hH : H ≠ ⊤) :
    q.prime * ((q.order ^ 2 - 1) * q.order ^ (2 * s + 3)) ≤ H.index := by
  letI : Finite (CFSG.Models.TwistedA (s + 4) q) := twistedA_shifted_finite q (s + 1)
  obtain ⟨c, _, hcG⟩ := exists_radicalCentre_projective_ne_one q (s + 1)
  let a := (centralRadicalKernelEquiv q (s + 2)).symm c
  have ha : centralRadicalKernelEquiv q (s + 2) a = c :=
    (centralRadicalKernelEquiv q (s + 2)).apply_symm_apply c
  have hn : higherUnitaryProjectiveExtensionHom q s
      (SemidirectProduct.inl (centralRadicalHom q (s + 2) a)) ≠ 1 := by
    rw [higherExtension_central_apply]
    rw [← projectiveRadicalCentreHom_equiv_apply, ha]
    exact hcG
  exact higherCoupledIndex_of_central_survival q s
    (higherUnitaryProjectiveExtensionHom q s) a hn H hH

theorem twistedA_higher_coupled_proper_index (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H ≠ ⊤) :
    q.prime * (q.order ^ 2 - 1) * q.order ^ (2 * r - 5) ≤ H.index := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  subst r
  have he : 2 * (s + 4) - 5 = 2 * s + 3 := by omega
  simpa only [he, mul_assoc] using twistedA_shifted_higher_coupled_proper_index q s H hH

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
