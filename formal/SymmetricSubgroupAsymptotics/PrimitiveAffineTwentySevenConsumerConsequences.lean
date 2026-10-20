import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenCatalogueOrders
import SymmetricSubgroupAsymptotics.StandardGLThreeIndexTwoRecognition
import SymmetricSubgroupAsymptotics.SmallAffineTwentySevenOrderSolvability
import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace
import SymmetricSubgroupAsymptotics.ChiefAbelianSeriesTransport

/-! The exact primitive degree27 consumers from the already-retained broader
composition catalogue. Small complements retain their actual order and
solvability; the two large alternatives retain actual matrix-image isomorphisms.
The nine literal soluble row isomorphisms are not asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open StandardThreeDimensionalLinearGroups

inductive AffineTwentySevenComplementAlternative
    (L : Type) [Group L] [Finite L] : Type
  | small (order_le : Nat.card L ≤ 78) (soluble : IsSolvable L)
  | special (equiv : L ≃* SpecialThree 3)
  | general (equiv : L ≃* GeneralThree 3)

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 27)]
    [FaithfulSMul G (Fin 27)]

def affineTwentySevenComplementAlternative
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (P : PrimitiveAffineProfile G (Fin 27))
    (hprimitive : MulAction.IsPreprimitive G (Fin 27)) (x : Fin 27) :
    AffineTwentySevenComplementAlternative (P.complement x) := by
  apply Classical.choice
  obtain h | h | h | h | h | h | h | h | h :=
    P.complement_order_cases_degreeTwentySeven catalogue hprimitive x
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order (Or.inl h))
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order (Or.inr (Or.inl h)))
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inl h))))
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · refine ⟨?_⟩
    exact .small (by omega) (isSolvable_of_small_twentySeven_complement_order
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  · refine ⟨?_⟩
    exact .special (equivSpecialThree_of_card5616
      (P.complementLinearMap_degreeTwentySeven hprimitive x)
      (P.complementLinearMap_degreeTwentySeven_injective hprimitive x) h)
  · refine ⟨?_⟩
    exact .general (equivGeneralThree_of_card11232
      (P.complementLinearMap_degreeTwentySeven hprimitive x)
      (P.complementLinearMap_degreeTwentySeven_injective hprimitive x) h)

theorem primitiveAffineTwentySeven_soluble_complement_card_le
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (P : PrimitiveAffineProfile G (Fin 27))
    (hprimitive : MulAction.IsPreprimitive G (Fin 27)) (x : Fin 27)
    (hsoluble : IsSolvable (P.complement x)) : Nat.card (P.complement x) ≤ 78 := by
  letI := hsoluble
  cases affineTwentySevenComplementAlternative catalogue P hprimitive x with
  | small h _ => exact h
  | special e =>
      exact ((nonsolvable_specialThree ProjectiveThreeSimplicity.proved)
        (solvable_of_surjective (f := e.toMonoidHom) e.surjective)).elim
  | general e =>
      exact ((nonsolvable_generalThree ProjectiveThreeSimplicity.proved)
        (solvable_of_surjective (f := e.toMonoidHom) e.surjective)).elim

theorem primitiveAffineTwentySeven_nonsoluble_abelianLength_le_one
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (P : PrimitiveAffineProfile G (Fin 27))
    (hprimitive : MulAction.IsPreprimitive G (Fin 27)) (x : Fin 27)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsoluble : ¬ IsSolvable (P.complement x)) : T.envelope.abelianLength ≤ 1 := by
  cases affineTwentySevenComplementAlternative catalogue P hprimitive x with
  | small _ hs => exact (hnonsoluble hs).elim
  | special e =>
      have h := (specialThreeCertificate ProjectiveThreeSimplicity.proved).chief_bound
        (actualChiefSeriesComap e.symm T.chief)
      rw [actualChiefSeriesComap_abelianLength e.symm T.chief] at h
      rw [T.abelianLength_eq]
      omega
  | general e =>
      have h := (generalThreeCertificate ProjectiveThreeSimplicity.proved).chief_bound
        (actualChiefSeriesComap e.symm T.chief)
      rw [actualChiefSeriesComap_abelianLength e.symm T.chief] at h
      exact T.abelianLength_eq.trans_le h

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
