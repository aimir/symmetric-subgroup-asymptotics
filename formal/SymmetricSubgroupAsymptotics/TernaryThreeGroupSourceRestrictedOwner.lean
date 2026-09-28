import SymmetricSubgroupAsymptotics.FusionSourceRestriction
import SymmetricSubgroupAsymptotics.TernaryThreeGroupPhysicalOwner

/-!
# Source-retained degree-nine ternary owner

The sharp degree-nine row is valid only on the one-regular-`C3`,
no-natural-`A4` source state.  Here that state is built into the local
physical predicate itself.  The generic source-restriction theorem then
supplies the required surviving-map implication automatically.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A degree-nine ternary action with the marked source built into its
physical predicate has the sharp `8/9` original-weight row. -/
theorem degreeNine_sourceRestricted_ternaryPGroup_physical_owner_bound
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (U : Subgroup (Equiv.Perm (Fin 9)))
    [MulAction.IsPretransitive U (Fin 9)] (hU : IsPGroup 3 U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hRestricted : FusionOrbitNatural U
      (FusionSourceRestrictedPredicate U P C1DegreeNineSourcePattern)) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U
            (FusionSourceRestrictedPredicate U P
              C1DegreeNineSourcePattern))) : ℝ) /
          exactBenchmark (b + 9) ≤
        c1EarlierKernel b .degreeNine D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 9)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  apply degreeNine_marked_ternaryPGroup_physical_owner_bound
    hChief hPrimitive h18 U hU b
      (FusionSourceRestrictedPredicate U P C1DegreeNineSourcePattern)
      hRestricted
  intro N J β h
  exact fusionSourceRestrictedPredicate_encode_source U P
    C1DegreeNineSourcePattern N J β h

end SymmetricSubgroupAsymptotics

end
