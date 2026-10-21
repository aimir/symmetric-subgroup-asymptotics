import SymmetricSubgroupAsymptotics.GLThreeThreeNonsolubleOrders
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenLinearEmbedding
import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace
import SymmetricSubgroupAsymptotics.ChiefAbelianSeriesTransport

/-! The actual nonsoluble degree27 complement has abelian chief length
at most one, without the336-row correspondence. The actual faithful
linear image, Sylow13 argument and determinant-kernel recognition produce
the two linear-group isomorphisms used by the existing chief certificates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open StandardThreeDimensionalLinearGroups

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 27)]
    [FaithfulSMul G (Fin 27)]

theorem primitiveAffineTwentySeven_nonsoluble_abelianLength_le_one_without_catalogue
    (P : PrimitiveAffineProfile G (Fin 27))
    (hprimitive : MulAction.IsPreprimitive G (Fin 27)) (x : Fin 27)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsoluble : ¬IsSolvable (P.complement x)) : T.envelope.abelianLength≤1 := by
  let f := P.complementLinearMap_degreeTwentySeven hprimitive x
  have hf := P.complementLinearMap_degreeTwentySeven_injective hprimitive x
  rcases GLThreeThreeNonsolubleOrders.nonsoluble_order f hf hnonsoluble with hS|hG
  · let e := equivSpecialThree_of_card5616 f hf hS
    have h := (specialThreeCertificate ProjectiveThreeSimplicity.proved).chief_bound
      (actualChiefSeriesComap e.symm T.chief)
    rw [actualChiefSeriesComap_abelianLength e.symm T.chief] at h
    rw [T.abelianLength_eq]
    omega
  · let e := equivGeneralThree_of_card11232 f hf hG
    have h := (generalThreeCertificate ProjectiveThreeSimplicity.proved).chief_bound
      (actualChiefSeriesComap e.symm T.chief)
    rw [actualChiefSeriesComap_abelianLength e.symm T.chief] at h
    exact T.abelianLength_eq.trans_le h

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
