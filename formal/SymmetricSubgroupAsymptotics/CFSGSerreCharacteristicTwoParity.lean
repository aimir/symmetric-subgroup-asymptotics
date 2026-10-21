import SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoRoots
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder

/-! Every nontrivial quotient of an original characteristic-two Serre
model has even cardinality. The argument uses an actual surviving root
involution, not a model identification or a finite simple-group order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoParity
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
  (K : Type) [Field K] [CharP K 2]

theorem modelRoot_sq (negative : Bool) (i : Fin n) (t : K) :
    modelRoot A K negative i t ^ 2 = 1 := by
  apply Subtype.ext
  exact CFSGSerreCharacteristicTwoRoots.rootEquiv_sq A K negative i t

theorem quotient_even_card {G : Type*} [Group G] [Nontrivial G]
    (f : Model A K →* G) (hf : Function.Surjective f) : Even (Nat.card G) := by
  obtain ⟨negative, i, t, hne⟩ := exists_root_image_ne_one A K f hf
  have hs : f (modelRoot A K negative i t) ^ 2 = 1 := by
    rw [← map_pow, modelRoot_sq A K negative i t, map_one]
  by_contra heven
  exact hne (CFSGReduction.eq_one_of_square_eq_one_of_odd_card
    (Nat.not_even_iff_odd.mp heven) _ hs)

theorem projective_even_card [Nontrivial (Projective A K)] :
    Even (Nat.card (Projective A K)) :=
  quotient_even_card A K (QuotientGroup.mk' (Subgroup.center (Model A K)))
    (QuotientGroup.mk'_surjective (Subgroup.center (Model A K)))

end SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoParity
