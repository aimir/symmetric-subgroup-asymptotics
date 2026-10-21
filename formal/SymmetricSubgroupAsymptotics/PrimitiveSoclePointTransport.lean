import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-! Relabel only the points of an actual nonaffine full-socle chart.
The ambient group, full socle, simple factors and outer quotient map are
literally unchanged. No new primitive classification is invoked. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

def NonaffineData.transportPoints
    {G X Y : Type} [Group G] [Finite G] [Finite X] [Finite Y]
    [MulAction G X] [MulAction G Y] (D : NonaffineData G X)
    (e : X ≃ Y) (he : ∀ g : G,∀ x : X,e (g • x) = g • e x) :
    NonaffineData G Y where
  Simple := D.Simple
  group := D.group
  finite := D.finite
  simple := D.simple
  noncommutative := D.noncommutative
  factorCount := D.factorCount
  factorCount_pos := D.factorCount_pos
  socleEquiv := D.socleEquiv
  quotientEmbedding := D.quotientEmbedding
  quotientEmbedding_injective := D.quotientEmbedding_injective
  socle_transitive := by
    letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.socle_transitive
    refine ⟨fun y z => ?_⟩
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (finiteGroupSocle G) (e.symm y) (e.symm z)
    refine ⟨g,?_⟩
    change (g : G) • e.symm y = e.symm z at hg
    have hh := congrArg e hg
    rw [he,e.apply_symm_apply,e.apply_symm_apply] at hh
    exact hh
  indexForm := by
    have hc : Nat.card Y = Nat.card X := (Nat.card_congr e).symm
    simpa only [hc] using D.indexForm

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
