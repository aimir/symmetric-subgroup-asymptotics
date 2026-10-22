import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation

/-! All four sign combinations commute at two actual orthogonal Serre
nodes. Mixed signs use the literal original EF relation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreOrthogonalNodeCommutation
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreCrossNodeCommutation
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem rootVector_lie_zero_all_signs (i j : Fin n) (hne : i ≠ j) (hij : A i j = 0)
    (e f : Bool) : ⁅rootVector A e i, rootVector A f j⁆ = 0 := by
  cases e <;> cases f
  · exact rootVector_lie_zero_of_cartan_zero A false i j hij
  · simpa only [rootVector, Bool.false_eq_true, if_false, if_true] using generator_EF_ne A i j hne
  · have h := generator_EF_ne A j i (Ne.symm hne)
    change ⁅generator A (CartanMatrix.Generators.F i), generator A (CartanMatrix.Generators.E j)⁆ = 0
    rw [← lie_skew (generator A (CartanMatrix.Generators.F i))
      (generator A (CartanMatrix.Generators.E j)), h, neg_zero]
  · exact rootVector_lie_zero_of_cartan_zero A true i j hij

theorem modelRoots_commute_all_signs (K : Type) [Field K]
    (i j : Fin n) (hne : i ≠ j) (hij : A i j = 0) (e f : Bool) (a b : K) :
    Commute (CFSGSerreModelRootGeneration.modelRoot A K e i a)
      (CFSGSerreModelRootGeneration.modelRoot A K f j b) :=
  modelRoots_commute_of_lie_zero A K e f i j
    (rootVector_lie_zero_all_signs A i j hne hij e f) a b

end SymmetricSubgroupAsymptotics.CFSGSerreOrthogonalNodeCommutation
