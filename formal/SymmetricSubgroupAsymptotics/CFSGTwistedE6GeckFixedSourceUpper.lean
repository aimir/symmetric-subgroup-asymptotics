import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveCoordinateLifts

/-! The actual upper elements represented by ORIGINAL fixed-source
actions form a subgroup. Every such element is genuinely twist fixed;
the singleton and paired coordinate representatives belong to it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSourceUpper
open CFSGTwistedE6GeckPositiveActionInjective CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6WeylChamber CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists

def fixedSourceUpper (q : CFSG.PrimePower) : Subgroup (Positive (q.Extension 2)) :=
  (imageAction q).range.comap (positiveAction (q.Extension 2))

theorem mem_fixedSourceUpper_iff (q : CFSG.PrimePower) (u : Positive (q.Extension 2)) :
    u∈fixedSourceUpper q ↔ ∃s : Fixed q,imageAction q s=positiveAction (q.Extension 2) u := Iff.rfl

theorem fixedSourceUpper_fixed (q : CFSG.PrimePower) (u : Positive (q.Extension 2))
    (hu : u∈fixedSourceUpper q) :
    positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u := by
  obtain ⟨s,hs⟩ := (mem_fixedSourceUpper_iff q u).mp hu
  exact positive_fixed_of_original_witness q u s hs

theorem singleton_mem_fixedSourceUpper (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (x : RootLine (q.Extension 2) k.val)
    (hx : unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) x.val=x.val) :
    rootLinePositive (q.Extension 2) k x∈fixedSourceUpper q :=
  (mem_fixedSourceUpper_iff q _).mpr (singleton_positive_witness q k hk x hx)

theorem pair_mem_fixedSourceUpper (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val≠k.val) (x : RootLine (q.Extension 2) k.val) :
    rootLinePositive (q.Extension 2) k x*
      positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2)
        (rootLinePositive (q.Extension 2) k x)∈fixedSourceUpper q :=
  (mem_fixedSourceUpper_iff q _).mpr (paired_positive_witness q k hk x)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSourceUpper
