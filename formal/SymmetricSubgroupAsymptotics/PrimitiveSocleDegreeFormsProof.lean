import SymmetricSubgroupAsymptotics.PrimitiveSocleFullStructure
import SymmetricSubgroupAsymptotics.PrimitiveSocleStabilizerDegreeForms

/-! The full primitive socle has the exact raw O'Nan--Scott degree forms.
All structural steps use the original finite action and actual full socle. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

/-- The regular two-minimal-normal branch was retained by FullStructure;
the unique-minimal branch is settled by its actual point stabilizer. -/
theorem PrimitiveFullSocleChart.indexForm
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : PrimitiveFullSocleChart G X) :
    (∃ H : Subgroup D.Simple, H≠⊤ ∧ Nat.card X=H.index^D.factorCount) ∨
    (∃ a : ℕ, D.factorCount≤2*a ∧ Nat.card X=Nat.card D.Simple ^ a) := by
  rcases D.degreeOrMinimal with hmin|hdegree
  · letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.transitive
    letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
    let x : X := Classical.choice inferInstance
    exact minimalNormal_pointStabilizer_degree_forms (finiteGroupSocle G) hmin
      (isCenterless_of_simple_perfect D.Simple) D.factorCount D.equiv x
  · exact Or.inr hdegree

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
