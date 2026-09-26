import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Data.Nat.Log

/-! The retained rank increment and derived-normal head increment share
the actual first-axis order budget. Characters extending to the original
subdirect group annihilate every original derived normal. This retains the
extendibility cut and gives the coupled transition for nonabelian cores. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (K : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))

/-- Forget only the two subspace memberships, not the original axis. -/
def subdirectRetainedPrimeMap :
    letI := Subgroup.normal_goursatFst hA
    subdirectRetainedCharacters p K hA →ₗ[ZMod p] PrimeCharacters p K.goursatFst := by
  letI := Subgroup.normal_goursatFst hA
  exact (primeRelativeCharacters p K.goursatFst).subtype.comp
    (subdirectRetainedCharacters p K hA).subtype

theorem subdirectRetainedPrimeMap_injective :
    Function.Injective (subdirectRetainedPrimeMap p K hA) :=
  Subtype.val_injective.comp Subtype.val_injective

/-- The actual retained characters vanish on a derived normal's literal
axis, since they extend to the whole original group K. -/
theorem subdirectRetainedPrimeMap_vanishes
    (M : Subgroup K) (hM : M ≤ commutator K) :
    letI := Subgroup.normal_goursatFst hA
    ∀ v l, subdirectRetainedPrimeMap p K hA v
      (Additive.ofMul (Subgroup.inclusion (SubdirectNormalHead.firstAxis_le K M) l)) = 0 := by
  letI := Subgroup.normal_goursatFst hA
  rintro ⟨v,hv⟩ l
  obtain ⟨χ,rfl⟩ := hv
  obtain ⟨ha,hm⟩ := (SubdirectNormalHead.mem_firstAxis K M (l : A)).mp l.2
  have hz := Abelianization.commutator_subset_ker
    (AddMonoidHom.toMultiplicativeRight χ) (hM hm)
  change χ (Additive.ofMul (⟨((l : A),1),ha⟩ : K)) = 0 at hz
  exact hz

/-- The complete axis character rank is safe as an upper bound here:
the retained characters consume the complementary part of the same order. -/
theorem subdirectRetained_firstAxis_pow_le (M : Subgroup K)
    (hM : M ≤ commutator K) :
    letI := Subgroup.normal_goursatFst hA
    p ^ (Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) +
      Module.finrank (ZMod p) (PrimeCharacters p (SubdirectNormalHead.firstAxis K M))) ≤
        Nat.card K.goursatFst := by
  letI := Subgroup.normal_goursatFst hA
  exact retainedCharacters_subgroup_rank_bound p (subdirectRetainedPrimeMap p K hA)
    (subdirectRetainedPrimeMap_injective p K hA)
    (Subgroup.inclusion (SubdirectNormalHead.firstAxis_le K M))
    (Subgroup.inclusion_injective _) (subdirectRetainedPrimeMap_vanishes p K hA M hM)

/-- The same coupled inequality for the whole-first-factor relative head. -/
theorem subdirectRetained_firstAxis_relative_pow_le (M : Subgroup K) [M.Normal]
    (hM : M ≤ commutator K) :
    letI := Subgroup.normal_goursatFst hA
    letI := SubdirectNormalHead.firstAxis_normal K M hA
    p ^ (Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) +
      Module.finrank (ZMod p)
        (primeRelativeCharacters p (SubdirectNormalHead.firstAxis K M))) ≤
        Nat.card K.goursatFst := by
  letI := Subgroup.normal_goursatFst hA
  letI := SubdirectNormalHead.firstAxis_normal K M hA
  apply le_trans _ (subdirectRetained_firstAxis_pow_le p K hA M hM)
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (Nat.add_le_add_left (Submodule.finrank_le _) _)

/-- The actual derived-normal maximum attains a normal whose first axis
annihilates the retained rank increment. Natural subtraction is the positive
part of the rank difference, so no monotonicity of rho is assumed. -/
theorem primeSubdirect_joint_pow_le
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    letI := Subgroup.normal_goursatFst hA
    p ^ (Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) +
      (primeDerivedNormalRank p K - primeDerivedNormalRank p B)) ≤
        Nat.card K.goursatFst := by
  letI := Subgroup.normal_goursatFst hA
  obtain ⟨M,hMn,hMd,hMeq⟩ := primeDerivedNormalRank_attained p K
  letI := hMn
  letI := SubdirectNormalHead.firstAxis_normal K M hA
  letI := SubdirectNormalHead.secondImage_normal K M hB
  have hr := SubdirectNormalHead.relativeHead_le K M p hA hB
  have hs := primeRelativeHead_le_normalHeadMax p (commutator B)
    (SubdirectNormalHead.secondImage K M)
    (SubdirectNormalHead.secondImage_le_commutator K M hMd)
  have he : primeDerivedNormalRank p K - primeDerivedNormalRank p B ≤
      Module.finrank (ZMod p)
        (primeRelativeCharacters p (SubdirectNormalHead.firstAxis K M)) := by
    change Module.finrank (ZMod p) (primeRelativeCharacters p M) = _ at hMeq
    change _ ≤ primeDerivedNormalRank p B at hs
    omega
  exact (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (Nat.add_le_add_left he _)).trans
      (subdirectRetained_firstAxis_relative_pow_le p K hA M hMd)

include hA in
/-- Natural differences retain the nonnegative actual character increment
and the positive part of the derived-normal increment, as in the mixture. -/
theorem primeSubdirect_joint_le_log
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    (Module.finrank (ZMod p) (PrimeCharacters p K) -
      Module.finrank (ZMod p) (PrimeCharacters p B)) +
      (primeDerivedNormalRank p K - primeDerivedNormalRank p B) ≤
        Nat.log p (Nat.card K.goursatFst) := by
  letI := Subgroup.normal_goursatFst hA
  have he := primeCharacterRank_subdirect_eq p K hA hB
  have h := Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (primeSubdirect_joint_pow_le p K hA hB)
  omega

/-- Three coupled constraints on every actual full subdirect pair core.
No direct-product replacement or independently maximized pair is used. -/
theorem primeSubdirect_joint_constraints
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    letI := Subgroup.normal_goursatFst hA
    let δ := Module.finrank (ZMod p) (PrimeCharacters p K) -
      Module.finrank (ZMod p) (PrimeCharacters p B)
    let ε := primeDerivedNormalRank p K - primeDerivedNormalRank p B
    Module.finrank (ZMod p) (PrimeCharacters p B) ≤
      Module.finrank (ZMod p) (PrimeCharacters p K) ∧
    δ ≤ Module.finrank (ZMod p) (primeRelativeCharacters p K.goursatFst) ∧
    ε ≤ primeSubdirectAxisNormalRank p K ∧
    δ + ε ≤ Nat.log p (Nat.card K.goursatFst) := by
  letI := Subgroup.normal_goursatFst hA
  have he := primeCharacterRank_subdirect_eq p K hA hB
  have hd := primeCharacterRank_subdirect_le p K hA hB
  have hr := primeDerivedNormalRank_subdirect_le p K hA hB
  have hj := primeSubdirect_joint_le_log p K hA hB
  dsimp only
  omega

end SymmetricSubgroupAsymptotics
