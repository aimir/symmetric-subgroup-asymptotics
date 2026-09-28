import SymmetricSubgroupAsymptotics.C1OriginalNormalEpiSum
import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseQuotient
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank

/-!
# The exact numerical interface for the ternary prime-base owner

Every target in this file is an actual quotient of the literal natural
`A4` top.  The regular-module reduction has already retained the complete
source and therefore asks for the joint mass

`sum_beta |Hom(ker beta, F3)|`.

The two genuinely numerical inputs are exposed separately:

* the number of onto top maps has the degree-six exponent `8 / 15`;
* every one of their literal kernels has ternary character rank at most
  one third of the original permutation degree.

The theorems below prove that these two inputs give the degree-twelve
exponent `16 / 15`, for every actual original normal axis, and install the
result in the original-weight physical consumer.  No classification of
the quotients of `A4`, split extension, or replacement source is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

open TernaryA4InvariantSubmodules

/-- The checked structural datum saying that the target is an actual
quotient of the literal natural `A4` top.  Keeping the map, rather than a
list of abstract quotient isomorphism types, is useful on original normal
axes. -/
abbrev A4QuotientMap (S : Type*) [Group S] := GroupEpimorphism A4 S

/-- The missing top-map input in exactly the exponent convention used by
the degree-six row.  The target remains the actual quotient `S`. -/
def A4QuotientTopEpiInput (b : ℕ) (J S : Type) [Group J] [Group S]
    [Finite J] [Finite S] (D : ℝ) : Prop :=
  (Nat.card (GroupEpimorphism J S) : ℝ) ≤
    D * (2 : ℝ) ^ (((8 : ℝ) / 15) * b)

/-- The missing permutation-rank input, stated on every literal kernel of
every actual onto top map.  This is stronger and more reusable than an
unmarked bound on an abstract subgroup of the source. -/
def A4QuotientKernelThirdInput (b : ℕ) (J S : Type) [Group J] [Group S]
    [Finite J] [Finite S] : Prop :=
  ∀ β : GroupEpimorphism J S,
    3 * Module.finrank (ZMod 3) (PrimeCharacters 3 β.1.ker) ≤ b

/-- The internally proved permutation-group theorem supplies the kernel
premise on every literal source, with no external quotient-rank assumption. -/
theorem a4QuotientKernelThirdInput_internal
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (S : Type) [Group S] [Finite S] :
    A4QuotientKernelThirdInput b J S := by
  intro β
  exact groupEpimorphismKernel_three_mul_rank_le_degree J β

/-- The rational envelope converting one ternary character coordinate
per three source points into the exponent `8 / 15`. -/
theorem ternaryPower_le_primeBase_eight_fifteenths (b d : ℕ)
    (hd : 3 * d ≤ b) :
    (3 : ℝ) ^ d ≤ (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
  calc
    _ ≤ ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ d :=
      pow_le_pow_left₀ (by norm_num) c1_three_le_binary_envelope d
    _ = (2 : ℝ) ^ (((8 : ℝ) / 5) * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hd' : (3 : ℝ) * d ≤ b := by exact_mod_cast hd
      linarith

/-- A cast-safe version of the exact character-mass rank estimate. -/
theorem regularTopCharacterMass_cast_le_of_rank
    {J S : Type} [Group J] [Group S] [Finite J] [Finite S]
    (d : ℕ)
    (hrank : ∀ β : GroupEpimorphism J S,
      Module.finrank (ZMod 3) (PrimeCharacters 3 β.1.ker) ≤ d) :
    (regularTopCharacterMass 3 J S : ℝ) ≤
      (Nat.card (GroupEpimorphism J S) : ℝ) * (3 : ℝ) ^ d := by
  exact_mod_cast regularTopCharacterMass_le_of_rank 3 d hrank

/-- The two exact numerical inputs give the full `16 / 15` joint mass.
The `A4` quotient map is retained in the statement even though the scalar
argument only needs its two audited consequences. -/
theorem a4Quotient_regularTopCharacterMass_le
    {J S : Type} [Group J] [Group S] [Finite J] [Finite S]
    (_q : A4QuotientMap S) (b d : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (htop : A4QuotientTopEpiInput b J S D)
    (hrank : ∀ β : GroupEpimorphism J S,
      Module.finrank (ZMod 3) (PrimeCharacters 3 β.1.ker) ≤ d)
    (hbudget : 3 * d ≤ b) :
    (regularTopCharacterMass 3 J S : ℝ) ≤
      D * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) := by
  have hmass := regularTopCharacterMass_cast_le_of_rank d hrank
  have hpow := ternaryPower_le_primeBase_eight_fifteenths b d hbudget
  calc
    _ ≤ (Nat.card (GroupEpimorphism J S) : ℝ) * (3 : ℝ) ^ d := hmass
    _ ≤ (D * (2 : ℝ) ^ (((8 : ℝ) / 15) * b)) *
        (2 : ℝ) ^ (((8 : ℝ) / 15) * b) :=
      mul_le_mul htop hpow (by positivity) (mul_nonneg hD (by positivity))
    _ = D * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- The direct one-third formulation used by permutation-source
applications.  The floor is internal and cannot lose an exponent. -/
theorem a4Quotient_regularTopCharacterMass_le_of_third
    {J S : Type} [Group J] [Group S] [Finite J] [Finite S]
    (q : A4QuotientMap S) (b : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (htop : A4QuotientTopEpiInput b J S D)
    (hkernel : A4QuotientKernelThirdInput b J S) :
    (regularTopCharacterMass 3 J S : ℝ) ≤
      D * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) := by
  apply a4Quotient_regularTopCharacterMass_le q b (b / 3) D hD htop
  · intro β
    have h := hkernel β
    omega
  · omega

namespace C1TernaryPrimeBaseOwnerWitness

/-- Every arbitrary original normal axis has the literal `A4` quotient
map required by the numerical theorem. -/
def originalNormalA4QuotientMap
    {G : Type} [Group G] (W : C1TernaryPrimeBaseOwnerWitness G)
    (N : Subgroup G) [N.Normal] : A4QuotientMap (W.quotientTop N) :=
  ⟨W.topQuotient N, W.topQuotient_surjective N⟩

/-- Full original-weight installation of the prime-base numerical row.
Only the two source inequalities isolated above remain as premises.  The
arbitrary-normal chart and every regular embedding are supplied by the
checked structural owner itself. -/
theorem physical_owner_bound_of_numerical_inputs
    (U : Subgroup (Equiv.Perm (Fin 12)))
    (W : C1TernaryPrimeBaseOwnerWitness U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (C : {N : Subgroup U // N.Normal} → ℝ) (hC : ∀ N, 0 ≤ C N)
    (htop : ∀ (J : Subgroup (Equiv.Perm (Fin b)))
      (N : {N : Subgroup U // N.Normal}),
      A4QuotientTopEpiInput b J (U ⧸ (W.top.ker ⊔ N.1)) (C N)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + 12) ≤
      c1EarlierKernel b .degreeTwelve
        (∑ N : {N : Subgroup U // N.Normal},
          (originalNormalRegularConstant 3 W.top W.baseModule W.baseChart N : ℝ) * C N)
        (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  letI : Finite W.baseImage :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite ↥W.baseModule := by
    change Finite W.baseImage
    infer_instance
  apply c1EarlierPhysical_regular_owner_bound (p := 3) .degreeTwelve U
    W.top W.baseModule W.baseChart (fun N => by
      letI : N.1.Normal := N.2
      exact W.quotient_regular_embedding N.1) b P hP C
  intro J N
  letI : N.1.Normal := N.2
  have hm := a4Quotient_regularTopCharacterMass_le_of_third
    (W.originalNormalA4QuotientMap N.1) b (C N) (hC N) (htop J N)
    (a4QuotientKernelThirdInput_internal b J
      (U ⧸ (W.top.ker ⊔ N.1)))
  have hinflate :
      C N * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) ≤
        C N * ((b : ℝ) + 1) * (2 : ℝ) ^ (((16 : ℝ) / 15) * b) := by
    apply mul_le_mul_of_nonneg_right
    · nlinarith [hC N, (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
    · positivity
  simpa only [c1EarlierExponent] using hm.trans hinflate

end C1TernaryPrimeBaseOwnerWitness
end SymmetricSubgroupAsymptotics

end
