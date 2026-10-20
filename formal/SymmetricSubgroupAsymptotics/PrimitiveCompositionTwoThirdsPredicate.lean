import SymmetricSubgroupAsymptotics.PrimitiveCompositionActualOrder
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability

/-! Arithmetic alternatives for the two actual primitive actions used by
semisimple compression. The exceptional orders below are proved soluble,
so they cannot be the actual nonabelian simple socle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

abbrev TwoThirdsSolubleSimpleOrder (n : ℕ) : Prop :=
  n=5 ∨ n=7 ∨ n=11 ∨ n=21 ∨ n=56 ∨ n=72 ∨ n=216

theorem solvable_of_twoThirdsSolubleSimpleOrder
    (T : Type) [Group T] [Finite T]
    (h : TwoThirdsSolubleSimpleOrder (Nat.card T)) : IsSolvable T := by
  rcases h with h|h|h|h|h|h|h
  · exact burnsideTwoPrimeSolvability.solvable T 5 5 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable T 7 7 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable T 11 11 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable T 3 7 1 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable T 2 7 3 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable T 2 3 3 2 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable T 2 3 3 3 (by decide) (by decide) (by norm_num [h])

abbrev PrimitiveTwoThirdsRowReceipt (g t : PrimitiveCompositionBoundRow) : Prop :=
  ∀ q : Fin 15,0<q.val → g.kind=.orderBound → 5≤g.degree → g.degree<30 →
    5≤t.degree → t.degree≤g.degree →
    q.val*t.groupOrder=g.groupOrder → g.degree∣t.groupOrder →
    2^q.val≤t.degree^3 →
      3*q.val≤2*g.degree ∨ (g.degree=8 ∧ g.groupOrder=1344) ∨
      g.degree=16 ∨ TwoThirdsSolubleSimpleOrder t.groupOrder

end SymmetricSubgroupAsymptotics
