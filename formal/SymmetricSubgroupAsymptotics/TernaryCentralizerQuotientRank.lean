import SymmetricSubgroupAsymptotics.TernaryCentralizerOrbitRank
import SymmetricSubgroupAsymptotics.CoprimeTernaryCentralizerLift
import SymmetricSubgroupAsymptotics.TernaryKernelSylowSemiregular

/-!
# Central binary rank of original quotients with binary kernel

Coprime Sylow lifting supplies actual centralizer preimages for central
involutions of the quotient. The original ternary orbit action bounds
their rank. For a semiregular ternary subgroup on twenty-four points the
bound is four, including when the original quotient is nonbinary.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryCentralizerQuotientRank

/-- A surjection with binary kernel preserves enough of the original
ternary centralizer to bound central binary rank by its point orbits. -/
theorem central_finrank_le_of_binary_kernel
    {G X Q : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q] [Finite Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (P : Sylow 3 G)
    (hP : ∀ a : P, a ^ 3 = 1) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤
      Nat.card (TernaryNormalizerOrbitPrefix.Orbits (X := X) (P : Subgroup G)) / 2 := by
  apply TernaryCentralizerOrbitRank.central_finrank_le_of_lifts
    (P : Subgroup G) hP pi
  intro z
  let target : Subgroup.centralizer (P.map pi : Set Q) :=
    ⟨binaryCentralOmegaEmbedding z, fun q _ ↦ Subgroup.mem_center_iff.mp z.val.property q⟩
  obtain ⟨g, hg⟩ :=
    CoprimeTernaryCentralizerLift.centralizerMap_surjective pi hpi hker P target
  exact ⟨g, congrArg Subtype.val hg⟩

/-- A single factor of three in the group order determines the order of
every actual Sylow three subgroup. -/
theorem sylow_card_three
    {G : Type} [Group G] [Finite G]
    (hthree : 3 ∣ Nat.card G) (hnine : ¬ 9 ∣ Nat.card G)
    (P : Sylow 3 G) : Nat.card P = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hPthree : 3 ∣ Nat.card P := P.dvd_card_of_dvd_card hthree
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnlt : n < 2 := by
    by_contra h
    have hdiv : 9 ∣ Nat.card P := by
      rw [hn]
      exact pow_dvd_pow 3 (by omega : 2 ≤ n)
    exact hnine (hdiv.trans (P : Subgroup G).card_subgroup_dvd_card)
  have hnzero : n ≠ 0 := by
    intro h
    rw [hn, h] at hPthree
    norm_num at hPthree
  rw [hn, show n = 1 by omega, pow_one]

/-- The original twenty-four-point geometry yields central rank four
for every quotient whose literal original kernel is binary. -/
theorem central_finrank_le_four_of_semiregular_twentyFour
    {G X Q : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q] [Finite Q]
    (hX : Nat.card X = 24) (hthree : 3 ∣ Nat.card G) (hnine : ¬ 9 ∣ Nat.card G)
    (hfree : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hPcard : Nat.card P = 3 := sylow_card_three hthree hnine P
  have hP : ∀ a : (P : Subgroup G), a ^ 3 = 1 := fun a ↦ by
    calc
      a ^ 3 = a ^ Nat.card (P : Subgroup G) :=
        congrArg (fun n : ℕ ↦ a ^ n) hPcard.symm
      _ = 1 := pow_card_eq_one'
  have hfreeP : ∀ (a : P) (x : X), (a : G) • x = x → a = 1 := by
    intro a x hax
    by_contra ha
    exact hfree a (congrArg Subtype.val (hP a))
      (fun h ↦ ha (Subtype.ext h)) x hax
  have horbits := TernaryKernelSylowSemiregular.eight_orbits_of_semiregular_twentyFour
    (P : Subgroup G) hPcard hX hfreeP
  have h := central_finrank_le_of_binary_kernel (X := X) pi hpi hker P hP
  rwa [horbits] at h

end TernaryCentralizerQuotientRank
end SymmetricSubgroupAsymptotics

end
