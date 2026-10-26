import Mathlib.GroupTheory.Perm.Centralizer

/-! The actual centralizer cardinal for cycle type4,4 on eleven points.
The three fixed points contribute3!, the two four-cycles contribute4^2,
and their interchangeable multiplicity contributes2!. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElevenPointDoubleFourCentralizerCard

theorem card {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 11) (y : Equiv.Perm X)
    (hy : y.cycleType = Multiset.replicate 2 4) :
    Nat.card (Subgroup.centralizer ({y} : Set (Equiv.Perm X))) = 192 := by
  rw [Equiv.Perm.nat_card_centralizer,hy,hX]
  norm_num [Nat.factorial]

end SymmetricSubgroupAsymptotics.ElevenPointDoubleFourCentralizerCard
