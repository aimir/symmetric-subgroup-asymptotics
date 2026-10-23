import SymmetricSubgroupAsymptotics.CFSGTwistedA2PairNormalizerRestriction

/-! Actual inner alignment and retained inner torus. Its conjugation
action is injective because the original simple group has a genuinely
moved Sylow; no ambient unitary simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

private theorem conjugation_injective_of_nontrivial {G : Type*} [Group G]
    [IsSimpleGroup G] (w : G) (hw : MulAut.conj w ≠ 1) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rcases (inferInstance : (MulAut.conj : G →* MulAut G).ker.Normal).eq_bot_or_eq_top with h | h
  · exact (MulAut.conj : G →* MulAut G).ker_eq_bot_iff.mp h
  · have hh : w ∈ (MulAut.conj : G →* MulAut G).ker := by rw [h]; trivial
    exact False.elim (hw hh)

theorem rankTwo_inner_align_pair (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (f : MulAut (CFSG.Models.TwistedA 2 q)) :
    ∃ g : CFSG.Models.TwistedA 2 q, MulAut.conj g * f ∈ rankTwoPairStabilizer q hq := by
  obtain ⟨g, hP, hQ⟩ := rankTwoProjective_exists_inner_fix_pair q hq f
  refine ⟨g, ?_, ?_⟩
  · have he := congrArg (fun P : Sylow q.prime (CFSG.Models.TwistedA 2 q) =>
      (P : Subgroup (CFSG.Models.TwistedA 2 q))) hP
    exact he
  · have he := congrArg (fun P : Sylow q.prime (CFSG.Models.TwistedA 2 q) =>
      (P : Subgroup (CFSG.Models.TwistedA 2 q))) hQ
    change (((rankTwoProjectiveCover q hq (reversalFixed q 2) • rankTwoProjectiveSylow q hq :
      Sylow q.prime (CFSG.Models.TwistedA 2 q)) : Subgroup (CFSG.Models.TwistedA 2 q))).map
        (MulAut.conj g * f).toMonoidHom =
      ((rankTwoProjectiveCover q hq (reversalFixed q 2) • rankTwoProjectiveSylow q hq :
        Sylow q.prime (CFSG.Models.TwistedA 2 q)) : Subgroup (CFSG.Models.TwistedA 2 q)) at he
    rwa [rankTwoProjective_opposite_coe] at he

theorem rankTwo_inner_torus_mem_pair (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (t : (rankTwoProjectiveTorus q hq).range) :
    MulAut.conj t.val ∈ rankTwoPairStabilizer q hq := by
  have ht := (rankTwo_projective_pair_normalizer_eq_torus q hq).ge t.property
  constructor
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.1)
  · exact SetLike.coe_injective (Subgroup.mem_normalizer_iff_conj_image_eq.mp ht.2)

theorem rankTwo_inner_torus_injective (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] :
    Function.Injective (fun t : (rankTwoProjectiveTorus q hq).range => MulAut.conj t.val) := by
  have hw : MulAut.conj (rankTwoProjectiveCover q hq (reversalFixed q 2)) ≠ 1 := by
    intro he
    have hh := congrArg (fun a : MulAut (CFSG.Models.TwistedA 2 q) =>
      a • rankTwoProjectiveSylow q hq) he
    change (MulAut.conj (rankTwoProjectiveCover q hq (reversalFixed q 2))) •
      rankTwoProjectiveSylow q hq = (1 : MulAut (CFSG.Models.TwistedA 2 q)) •
        rankTwoProjectiveSylow q hq at hh
    rw [one_smul] at hh
    have hn := Sylow.smul_eq_iff_mem_normalizer.mp hh
    change rankTwoProjectiveCover q hq (reversalFixed q 2) ∈
      Subgroup.normalizer (((rankTwoUpperSubgroup q).map (rankTwoProjectiveCover q hq)) :
        Set (CFSG.Models.TwistedA 2 q)) at hn
    rw [rankTwo_projective_normalizer_eq_flag q hq] at hn
    exact rankTwoProjective_reversal_not_flag q hq hn
  intro t u he
  apply Subtype.ext
  exact conjugation_injective_of_nontrivial _ hw he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
