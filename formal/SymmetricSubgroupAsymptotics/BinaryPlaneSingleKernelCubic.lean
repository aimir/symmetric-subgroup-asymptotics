import SymmetricSubgroupAsymptotics.BinaryPlaneOddKernelMultiplicityUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A nonzero actual odd layer with one literal coordinate-kernel class
is one actual cyclic group of order three. Its displayed generator acts
nontrivially on every coordinate. No external cubic or F4 action is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCubic
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open RankOneCubicSylowCentralizer (Cubic cubicGenerator)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I]
    (C : Subgroup (W (R := R) (I := I))) (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)

include hsingle in
/-- Joint local faithfulness kills the common actual coordinate kernel. -/
theorem kernel_eq_bot (i : I) : localKernel C i = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply localLinear_joint C
  intro j
  have hj : g ∈ localKernel C j :=
    ((hsingle i).trans (hsingle j).symm) ▸ hg
  simpa only [map_one] using hj

include hsingle in
theorem localLinear_injective (i : I) : Function.Injective (localLinear C i) :=
  (localLinear C i).ker_eq_bot_iff.mp (kernel_eq_bot C i₀ hsingle i)

include hsingle in
/-- The cardinality is proved from the actual local cubic injection. -/
theorem card_eq_three (hO : oddKernel C ≠ ⊥) : Nat.card (oddKernel C) = 3 := by
  let f : oddKernel C → {p : Equiv.Perm (Fin 3) // p^3 = 1} :=
    fun g => ⟨toThree (localLinear C i₀ g),by rw [←map_pow,local_cubic,map_one]⟩
  have hf : Function.Injective f := by
    intro g h he
    exact localLinear_injective C i₀ hsingle i₀ (toThree_injective (congrArg Subtype.val he))
  have hsmall : Nat.card (oddKernel C) ≤ 3 := by
    have hc : Nat.card {p : Equiv.Perm (Fin 3) // p^3 = 1} = 3 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    exact (Nat.card_le_card_of_injective f hf).trans_eq hc
  letI : Nontrivial (oddKernel C) := (oddKernel C).nontrivial_iff_ne_bot.mpr hO
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hlarge : 3 ≤ Nat.card (oddKernel C) := by
    obtain hone | hdvd := (isPGroup_three C).card_eq_or_dvd
    · exfalso
      obtain ⟨g,hg⟩ := exists_ne (1 : oddKernel C)
      have hs : Subsingleton (oddKernel C) := (Nat.card_eq_one_iff_unique.mp hone).1
      exact hg (@Subsingleton.elim (oddKernel C) hs g 1)
    · exact Nat.le_of_dvd Nat.card_pos hdvd
  omega

/-- This equivalence belongs to the actual original odd subgroup. -/
def cubicEquiv (hO : oddKernel C ≠ ⊥) : oddKernel C ≃* Cubic := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact mulEquivOfPrimeCardEq (card_eq_three C i₀ hsingle hO)
    (by rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod])

abbrev generator (hO : oddKernel C ≠ ⊥) : oddKernel C :=
  BinaryPlaneRankOneOddGenerator.generator C (cubicEquiv C i₀ hsingle hO)

theorem generator_cube (hO : oddKernel C ≠ ⊥) : generator C i₀ hsingle hO ^ 3 = 1 :=
  BinaryPlaneRankOneOddGenerator.generator_cube C (cubicEquiv C i₀ hsingle hO)

include hsingle in
/-- The same actual generator is nonidentity in every local action. -/
theorem generator_local_nontrivial (hO : oddKernel C ≠ ⊥) (i : I) :
    localLinear C i (generator C i₀ hsingle hO) ≠ 1 := by
  intro he
  have hgen : generator C i₀ hsingle hO = 1 :=
    localLinear_injective C i₀ hsingle i (he.trans (map_one (localLinear C i)).symm)
  have hh := congrArg (cubicEquiv C i₀ hsingle hO) hgen
  have hn : cubicGenerator ≠ 1 := by decide +kernel
  apply hn
  simpa only [generator,BinaryPlaneRankOneOddGenerator.generator,
    MulEquiv.apply_symm_apply,map_one] using hh

include hsingle in
theorem generator_local_fixedFree (hO : oddKernel C ≠ ⊥) (i : I) (v : Plane)
    (hv : localLinear C i (generator C i₀ hsingle hO) v = v) : v = 0 :=
  BinaryPlaneNontrivialCubicFixedFree.fixedFree _
    (local_cubic C i (generator C i₀ hsingle hO))
    (generator_local_nontrivial C i₀ hsingle hO i) v hv

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCubic
