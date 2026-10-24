import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCoupledStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedA2HeisenbergModelIndex

/-! The actual rank-two unitary radical and actual unit torus act on
every original proper coset space. A surviving central element moves a
coset, and its SAME pulled-back stabilizer supplies both layer bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

abbrev rankTwoPointParabolic (q : CFSG.PrimePower) :=
  fixedRadical q 0 ⋊[rankTwoRadicalTorusAutHom q] (q.Extension 2)ˣ

def rankTwoExtensionHom (q : CFSG.PrimePower) :
    rankTwoPointParabolic q →* naturalFixed 2 q :=
  SemidirectProduct.lift (fixedRadical q 0).subtype (rankTwoNaturalTorus q)
    (fun _ => MonoidHom.ext (fun _ => rfl))

theorem rankTwoExtensionHom_inl (q : CFSG.PrimePower) (u : fixedRadical q 0) :
    rankTwoExtensionHom q (SemidirectProduct.inl u) = u.val := by
  simp only [rankTwoExtensionHom, SemidirectProduct.lift_inl]
  rfl

def rankTwoProjectiveExtensionHom (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    rankTwoPointParabolic q →* CFSG.Models.TwistedA 2 q :=
  (rankTwoProjectiveCover q hq).comp (rankTwoExtensionHom q)

theorem rankTwoProjectiveExtensionHom_inl (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (u : fixedRadical q 0) :
    rankTwoProjectiveExtensionHom q hq (SemidirectProduct.inl u) =
      rankTwoRadicalHom q hq u := by
  change rankTwoProjectiveCover q hq (rankTwoExtensionHom q (SemidirectProduct.inl u)) = _
  rw [rankTwoExtensionHom_inl]
  rfl

theorem rankTwo_coupled_degree_of_central_motion (q : CFSG.PrimePower)
    {X : Type*} [Finite X] [MulAction (rankTwoPointParabolic q) X]
    (x : X) (c : Multiplicative (centralParameters q 0))
    (hx : (SemidirectProduct.inl (centralRadicalHom q 0 c) : rankTwoPointParabolic q) • x ≠ x) :
    q.order ^ 3 ≤ Nat.card X ∨
      q.prime ^ 2 * q.order * (q.order - 1) ≤ Nat.card X ∨
        q.prime * q.order * (q.order + 1) ≤ (q.order + 1).gcd 3 * Nat.card X := by
  let M := MulAction.stabilizer (rankTwoPointParabolic q) x
  have hM : ¬ (centralRadicalHom q 0).range ≤ M.comap SemidirectProduct.inl := by
    intro he
    have hc : centralRadicalHom q 0 c ∈ M.comap SemidirectProduct.inl := he ⟨c, rfl⟩
    exact hx hc
  have hindex : M.index ≤ Nat.card X := by
    calc
      _ = Nat.card (MulAction.orbit (rankTwoPointParabolic q) x) :=
        (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (rankTwoPointParabolic q) x)).symm
      _ ≤ Nat.card X := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rcases rankTwo_semidirect_index_trichotomy q M hM with h | h | h
  · exact Or.inl (h.trans hindex)
  · exact Or.inr (Or.inl (h.trans hindex))
  · exact Or.inr (Or.inr (h.trans (Nat.mul_le_mul_left _ hindex)))

theorem twistedA_rankTwo_coupled_proper_index (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)]
    (H : Subgroup (CFSG.Models.TwistedA 2 q)) (hH : H ≠ ⊤) :
    q.order ^ 3 ≤ H.index ∨
      q.prime ^ 2 * q.order * (q.order - 1) ≤ H.index ∨
        q.prime * q.order * (q.order + 1) ≤ (q.order + 1).gcd 3 * H.index := by
  letI : Finite (CFSG.Models.TwistedA 2 q) := rankTwoModel_finite q
  obtain ⟨c, _, hcG⟩ := exists_rankTwoRadicalCentre_projective_ne_one q hq
  let a := (centralRadicalKernelEquiv q 0).symm c
  have ha : centralRadicalKernelEquiv q 0 a = c :=
    (centralRadicalKernelEquiv q 0).apply_symm_apply c
  have hn : rankTwoProjectiveExtensionHom q hq
      (SemidirectProduct.inl (centralRadicalHom q 0 a)) ≠ 1 := by
    rw [rankTwoProjectiveExtensionHom_inl]
    change rankTwoCentralParameterHom q hq a ≠ 1
    rw [← rankTwoRadicalCentreHom_equiv_apply, ha]
    exact hcG
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hn
  letI : MulAction (rankTwoPointParabolic q) (CFSG.Models.TwistedA 2 q ⧸ H) :=
    MulAction.compHom _ (rankTwoProjectiveExtensionHom q hq)
  have hb := rankTwo_coupled_degree_of_central_motion q x a hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
