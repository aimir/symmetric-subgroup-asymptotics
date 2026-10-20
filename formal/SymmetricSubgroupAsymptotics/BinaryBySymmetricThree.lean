import SymmetricSubgroupAsymptotics.NonPrimeAbelianSoclePart
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group
import Mathlib.GroupTheory.Nilpotent

/-!
# Actual binary extensions of the three-point symmetric group

An actual surjection to `S₃` with binary kernel has no quotient of order
three. Its nonbinary minimal normal subgroups are abelian, because each
embeds in `S₃`. If the ambient order has at most one factor of three, their
whole selected socle sum has order at most three and costs one normal
generator. These statements retain the displayed homomorphism and kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

/-- A finite binary kernel and the literal solvable `S₃` target make
the original group solvable. Surjectivity is unnecessary for this fact. -/
theorem isSolvable_of_binary_kernel_symmetricThree
    {Q : Type} [Group Q] [Finite Q]
    (beta : Q →* Equiv.Perm (Fin 3)) (hker : IsPGroup 2 beta.ker) :
    IsSolvable Q := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Group.IsNilpotent beta.ker := hker.isNilpotent
  letI : IsSolvable (Equiv.Perm (Fin 3)) :=
    ⟨⟨2, NaturalS4.derivedSeries_S3_two⟩⟩
  exact solvable_of_ker_le_range beta.ker.subtype beta
    (by rw [Subgroup.range_subtype])

/-- In a solvable ambient group, a minimal normal subgroup is abelian:
the nonabelian alternative would be both perfect and nontrivial solvable. -/
theorem minimalNormal_isMulCommutative_of_isSolvable
    {Q : Type} [Group Q] [Finite Q] [IsSolvable Q]
    (M : Subgroup Q) (hM : IsMinimalNormalSubgroup M) : IsMulCommutative M := by
  letI : M.Normal := hM.1
  letI : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.2.1
  by_contra hnoncomm
  letI : Group.IsPerfect M := nonabelian_minimal_normal_perfect M
    (fun K hK hKM ↦ by
      by_cases hbot : K = ⊥
      · exact Or.inl hbot
      · exact Or.inr (hM.2.2 K hK hbot hKM)) hnoncomm
  exact (ne_of_lt (IsSolvable.commutator_lt_top_of_nontrivial M))
    Group.IsPerfect.commutator_eq_top

/-- An intrinsic condition on actual normal quotients, stable under any
surjective image. It does not assert that every subgroup has this property. -/
def NoTernaryQuotient (Q : Type) [Group Q] : Prop :=
  ∀ (N : Subgroup Q) [N.Normal], N.index ≠ 3

theorem NoTernaryQuotient.of_surjective
    {Q B : Type} [Group Q] [Group B]
    (hQ : NoTernaryQuotient Q) (pi : Q →* B)
    (hpi : Function.Surjective pi) : NoTernaryQuotient B := by
  intro N _ hN
  apply hQ (N.comap pi)
  exact (N.index_comap_of_surjective (f := pi) hpi).trans hN

private theorem symmetricThree_product_of_involutions :
    ∀ g : Equiv.Perm (Fin 3), ∃ a b : Equiv.Perm (Fin 3),
      a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ g = a * b := by
  decide +kernel

/-- Every map from a displayed binary-by-`S₃` group to an order-three
group is trivial. Binary kernel elements vanish first; the remaining
three-point permutations are products of involutions. -/
theorem hom_eq_one_of_binary_kernel_symmetricThree
    {Q D : Type} [Group Q] [Group D]
    (beta : Q →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker) (hD : Nat.card D = 3)
    (f : Q →* D) : f = 1 := by
  letI : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have hDthree : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hkill : beta.ker ≤ f.ker := by
    intro x hx
    obtain ⟨n, hn⟩ := hker ⟨x, hx⟩
    have hxpow : f x ^ (2 ^ n) = 1 := by
      rw [← map_pow]
      exact (congrArg f (congrArg Subtype.val hn)).trans (map_one f)
    apply (hDthree.powEquiv
      ((by decide : Nat.Coprime 3 2).pow_right n)).injective
    change f x ^ (2 ^ n) = 1 ^ (2 ^ n)
    simpa only [one_pow] using hxpow
  let g : Equiv.Perm (Fin 3) →* D :=
    beta.liftOfSurjective hbeta ⟨f, hkill⟩
  have hg (x : Q) : g (beta x) = f x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have involution (a : Equiv.Perm (Fin 3)) (ha : a ^ 2 = 1) : g a = 1 := by
    apply (hDthree.powEquiv (by decide : Nat.Coprime 3 2)).injective
    change g a ^ 2 = 1 ^ 2
    rw [← map_pow, ha, map_one, one_pow]
  apply MonoidHom.ext
  intro x
  obtain ⟨a, b, ha, hb, hab⟩ := symmetricThree_product_of_involutions (beta x)
  change f x = 1
  rw [← hg x, hab, map_mul, involution a ha, involution b hb, one_mul]

/-- The order-three quotient obstruction is discharged by an actual
binary-kernel `S₃` quotient, not by a statement about possible simple types. -/
theorem noTernaryQuotient_of_binary_kernel_symmetricThree
    {Q : Type} [Group Q]
    (beta : Q →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker) : NoTernaryQuotient Q := by
  intro N _ hN
  let q := QuotientGroup.mk' N
  have hcard : Nat.card (Q ⧸ N) = 3 := hN
  have hq : q = 1 :=
    hom_eq_one_of_binary_kernel_symmetricThree beta hbeta hker hcard q
  have hsub : Subsingleton (Q ⧸ N) := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact (DFunLike.congr_fun hq a).trans (DFunLike.congr_fun hq b).symm
  letI : Subsingleton (Q ⧸ N) := hsub
  have hone : Nat.card (Q ⧸ N) = 1 := Nat.card_unique
  omega

/-- A nonbinary minimal normal subgroup embeds into the actual `S₃`
target and hence is solvable. Minimal normality then makes it abelian. -/
theorem nonbinary_minimal_isMulCommutative_of_binary_kernel_symmetricThree
    {Q : Type} [Group Q] [Finite Q]
    (beta : Q →* Equiv.Perm (Fin 3)) (hker : IsPGroup 2 beta.ker)
    (M : Subgroup Q) (hM : IsMinimalNormalSubgroup M)
    (hnot : ¬ IsPGroup 2 M) : IsMulCommutative M := by
  letI : M.Normal := hM.1
  have hinf : M ⊓ beta.ker = ⊥ := by
    by_contra hne
    have heq : M ⊓ beta.ker = M :=
      hM.2.2 (M ⊓ beta.ker) inferInstance hne inf_le_left
    have hle : M ≤ beta.ker := by rw [← heq]; exact inf_le_right
    exact hnot (hker.of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  let f : M →* Equiv.Perm (Fin 3) := beta.comp M.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have hm : (x : Q) ∈ M ⊓ beta.ker := ⟨x.property, hx⟩
    rw [hinf, Subgroup.mem_bot] at hm
    exact Subgroup.mem_bot.mpr (Subtype.ext hm)
  letI : IsSolvable (Equiv.Perm (Fin 3)) :=
    ⟨⟨2, NaturalS4.derivedSeries_S3_two⟩⟩
  letI : IsSolvable M := solvable_of_solvable_injective hf
  letI : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.2.1
  by_contra hnoncomm
  letI : Group.IsPerfect M := nonabelian_minimal_normal_perfect M
    (fun K hK hKM ↦ by
      by_cases hbot : K = ⊥
      · exact Or.inl hbot
      · exact Or.inr (hM.2.2 K hK hbot hKM)) hnoncomm
  exact (ne_of_lt (IsSolvable.commutator_lt_top_of_nontrivial M))
    Group.IsPerfect.commutator_eq_top

/-- At most one odd factor in a solvable ambient group's order bounds
the entire nonbinary socle sum. This passes directly to original quotients. -/
theorem nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart
    {Q : Type} [Group Q] [Finite Q] [IsSolvable Q] {a : ℕ}
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    MarkedC4.normalGen
      (minimalNormalSoclePart Q (fun M ↦ ¬ IsPGroup 2 M)) ≤ 1 := by
  let H := minimalNormalSoclePart Q (fun M ↦ ¬ IsPGroup 2 M)
  have hH : H = minimalNormalSoclePart Q
      (fun M ↦ ¬ IsPGroup 2 M ∧ IsMulCommutative M) := by
    apply minimalNormalSoclePart_congr
    intro M hM
    exact ⟨fun hnot ↦ ⟨hnot,
      minimalNormal_isMulCommutative_of_isSolvable M hM⟩, And.left⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card H) 2 := by
    rw [hH]
    exact abelianNonPrimarySoclePart_card_coprime Q 2
  have hdiv : Nat.card H ∣ 3 :=
    (hcop.pow_right a).dvd_of_dvd_mul_left
      ((Subgroup.card_subgroup_dvd_card H).trans hcard)
  have hp : IsPGroup 3 H := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone | hthree
    · exact IsPGroup.of_card (n := 0) (by simpa using hone)
    · exact IsPGroup.of_card (n := 1) (by simpa using hthree)
  have hrank : Module.finrank (ZMod 3) (PrimeCharacters 3 H) ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
    exact (primeCharacters_pow_finrank_le_card 3 H).trans
      (by simpa only [pow_one] using Nat.le_of_dvd (by decide : 0 < 3) hdiv)
  exact (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 3 H hp).trans hrank

/-- Specialization to a displayed binary-kernel `S₃` map. -/
theorem nonbinarySocle_normalGen_le_one_of_binary_kernel_symmetricThree
    {Q : Type} [Group Q] [Finite Q] {a : ℕ}
    (beta : Q →* Equiv.Perm (Fin 3)) (hker : IsPGroup 2 beta.ker)
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    MarkedC4.normalGen
      (minimalNormalSoclePart Q (fun M ↦ ¬ IsPGroup 2 M)) ≤ 1 := by
  letI : IsSolvable Q := isSolvable_of_binary_kernel_symmetricThree beta hker
  exact nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart hcard

end SymmetricSubgroupAsymptotics

end
