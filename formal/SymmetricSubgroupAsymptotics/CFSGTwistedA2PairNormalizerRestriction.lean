import SymmetricSubgroupAsymptotics.CFSGTwistedA2PairRestriction
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusNormalizerCard
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoPairNormalizer

/-! The literal opposite-pair stabilizer normalizes the intrinsic torus
after faithful restriction to the actual radical. The field factor is
then bounded by the proved intrinsic scalar reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

private theorem map_pair_normalizer {G : Type*} [Group G]
    (P Q : Subgroup G) (f : MulAut G) (hP : P.map f.toMonoidHom = P)
    (hQ : Q.map f.toMonoidHom = Q) :
    (Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (Q : Set G)).map f.toMonoidHom =
      Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.map_inf _ _ _ f.injective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective, hP, hQ]

private theorem normalizes_range_of_intertwines {S R Z : Type*} [Group S] [Group R] [Group Z]
    (rho : S →* MulAut R) (t : Z →* MulAut R)
    (h : ∀ (s : S) (z : Z), ∃ d : Z, ∀ r : R, rho s (t z r) = t d (rho s r))
    (s : S) : rho s ∈ Subgroup.normalizer (t.range : Set (MulAut R)) := by
  have hforward : ∀ (a : S) (A : MulAut R), A ∈ t.range →
      rho a * A * (rho a)⁻¹ ∈ t.range := by
    rintro a A ⟨z, rfl⟩
    obtain ⟨d, hd⟩ := h a z
    refine ⟨d, ?_⟩
    apply MulEquiv.ext
    intro r
    change t d r = rho a (t z ((rho a).symm r))
    rw [hd, (rho a).apply_symm_apply]
  apply Subgroup.mem_normalizer_iff.mpr
  intro A
  constructor
  · exact hforward s A
  · intro hA
    have he := hforward s⁻¹ _ hA
    have hc : rho s⁻¹ * (rho s * A * (rho s)⁻¹) * (rho s⁻¹)⁻¹ = A := by
      rw [map_inv]
      group
    rwa [hc] at he

theorem rankTwo_pairStabilizer_map_torus (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : rankTwoPairStabilizer q hq) :
    ((rankTwoProjectiveTorus q hq).range).map f.val.toMonoidHom =
      (rankTwoProjectiveTorus q hq).range := by
  have he := map_pair_normalizer (rankTwoUpperImage q hq) (rankTwoOppositeImage q hq)
    f.val f.property.1 f.property.2
  have hT := rankTwo_projective_pair_normalizer_eq_torus q hq
  exact (congrArg (fun H : Subgroup (CFSG.Models.TwistedA 2 q) => H.map f.val.toMonoidHom)
    hT.symm).trans (he.trans hT)

private theorem intertwines_of_embedding {G R Z : Type*} [Group G] [Group R] [Group Z]
    (e : R →* G) (he : Function.Injective e) (f : MulAut G) (a : MulAut R)
    (t : Z →* G) (b : Z →* MulAut R)
    (hfa : ∀ r : R, e (a r) = f (e r))
    (htb : ∀ (z : Z) (r : R), e (b z r) = t z * e r * (t z)⁻¹)
    (z : Z) (hstable : f (t z) ∈ t.range) :
    ∃ d : Z, ∀ r : R, a (b z r) = b d (a r) := by
  obtain ⟨d, hd⟩ := hstable
  refine ⟨d, ?_⟩
  intro r
  apply he
  rw [hfa, htb, htb, hfa, map_mul, map_mul, map_inv, hd]

theorem rankTwo_pairRestriction_mem_torus_normalizer (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : rankTwoPairStabilizer q hq) :
    rankTwoPairRestriction q hq f ∈ Subgroup.normalizer
      ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0))) := by
  apply normalizes_range_of_intertwines (rankTwoPairRestriction q hq) (rankTwoRadicalTorusAutHom q) ?_ f
  intro a z
  apply intertwines_of_embedding (rankTwoRadicalHom q hq) (rankTwoRadicalHom_injective q hq)
    a.val (rankTwoPairRestriction q hq a) (rankTwoProjectiveTorus q hq)
    (rankTwoRadicalTorusAutHom q)
  · intro r
    exact rankTwo_restrictRadical_intertwines q hq a.val a.property.1 r
  · intro d r
    exact rankTwoRadicalProjectiveEquiv_torus q hq d r
  · rw [← rankTwo_pairStabilizer_map_torus q hq a]
    exact ⟨_, ⟨z, rfl⟩, rfl⟩

theorem rankTwo_pairStabilizer_card_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] :
    Nat.card (rankTwoPairStabilizer q hq) ≤ (q.order ^ 2 - 1) * (2 * q.exponent) := by
  let j : rankTwoPairStabilizer q hq → Subgroup.normalizer
      ((rankTwoRadicalTorusAutHom q).range : Set (MulAut (fixedRadical q 0))) :=
    fun f => ⟨rankTwoPairRestriction q hq f, rankTwo_pairRestriction_mem_torus_normalizer q hq f⟩
  have hj : Function.Injective j := by
    intro f g he
    exact rankTwoPairRestriction_injective q hq (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective j hj).trans (rankTwo_torus_normalizer_card_le q hq)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
