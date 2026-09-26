import SymmetricSubgroupAsymptotics.PrimeRelativeRadical
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChainCapacity
import SymmetricSubgroupAsymptotics.PrimeSubdirectJointCapacity

/-! The actual evaluation-kernel axis consumes the part of the relative
head not already used by extendible characters. Its relative radical is
retained with full ambient conjugation, including nonabelian pair cores. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (K : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))

/-- The literal first axis inside the complete original evaluation kernel. -/
def subdirectEvaluationAxis : Subgroup A :=
  SubdirectNormalHead.firstAxis K (primeAbelianizationGroupMap p K).ker

include hA in
theorem subdirectEvaluationAxis_normal : (subdirectEvaluationAxis p K).Normal :=
  SubdirectNormalHead.firstAxis_normal K _ hA

theorem subdirectEvaluationAxis_le : subdirectEvaluationAxis p K ≤ K.goursatFst :=
  SubdirectNormalHead.firstAxis_le K _

/-- The radical kills restrictions of all K-characters, not only those
characters extending to the ambient factor A. -/
theorem subdirectRelativeRadical_le_evaluationAxis :
    letI := Subgroup.normal_goursatFst hA
    primeRelativeRadical p K.goursatFst ≤ subdirectEvaluationAxis p K := by
  letI := Subgroup.normal_goursatFst hA
  intro a ha
  obtain ⟨hN,hzero⟩ := (mem_primeRelativeRadical_iff p K.goursatFst a).mp ha
  refine (SubdirectNormalHead.mem_firstAxis K _ a).mpr
    ⟨Subgroup.mem_goursatFst.mp hN,?_⟩
  change primeAbelianizationMap p K
    (Additive.ofMul (⟨(a,1),Subgroup.mem_goursatFst.mp hN⟩ : K))=0
  ext χ
  exact hzero (subdirectRelativeCharacterMap p K hA
    (primeCharacterRestriction p (subdirectSecond K).ker χ))

/-- Retained characters vanish on the same literal evaluation-kernel axis. -/
theorem subdirectRetainedPrimeMap_vanishes_evaluationAxis :
    letI := Subgroup.normal_goursatFst hA
    ∀ v l, subdirectRetainedPrimeMap p K hA v
      (Additive.ofMul (Subgroup.inclusion (subdirectEvaluationAxis_le p K) l))=0 := by
  letI := Subgroup.normal_goursatFst hA
  rintro ⟨v,hv⟩ l
  obtain ⟨χ,rfl⟩ := hv
  obtain ⟨ha,hm⟩ := (SubdirectNormalHead.mem_firstAxis K _ (l : A)).mp l.2
  change primeAbelianizationMap p K (Additive.ofMul (⟨((l : A),1),ha⟩ : K))=0 at hm
  exact LinearMap.congr_fun hm χ

/-- The retained dimension and complete axis order share one exact budget. -/
theorem subdirectEvaluationAxis_card_bound :
    letI := Subgroup.normal_goursatFst hA
    p ^ Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) *
      Nat.card (subdirectEvaluationAxis p K) ≤ Nat.card K.goursatFst := by
  letI := Subgroup.normal_goursatFst hA
  exact retainedCharacters_subgroup_card_bound p (subdirectRetainedPrimeMap p K hA)
    (subdirectRetainedPrimeMap_injective p K hA)
    (Subgroup.inclusion (subdirectEvaluationAxis_le p K))
    (Subgroup.inclusion_injective _)
    (subdirectRetainedPrimeMap_vanishes_evaluationAxis p K hA)

/-- After the actual relative radical is removed, the retained dimension
and remaining quotient rank fit inside the original relative head. -/
theorem subdirectEvaluationAxis_quotient_rank_bound :
    letI := Subgroup.normal_goursatFst hA
    letI := subdirectEvaluationAxis_normal p K hA
    Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) +
      Module.finrank (ZMod p) (PrimeCharacters p
        (normalChainQuotient (primeRelativeRadical p K.goursatFst)
          (subdirectEvaluationAxis p K))) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p K.goursatFst) := by
  letI := Subgroup.normal_goursatFst hA
  letI := subdirectEvaluationAxis_normal p K hA
  let R := primeRelativeRadical p K.goursatFst
  let P := subdirectEvaluationAxis p K
  have hRP : R ≤ P := subdirectRelativeRadical_le_evaluationAxis p K hA
  have hbudget := subdirectEvaluationAxis_card_bound p K hA
  rw [primeRelativeRadical_card_factorization p K.goursatFst] at hbudget
  rw [← normalChainQuotient_card_mul R P hRP] at hbudget
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hquot : p ^ Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) *
      Nat.card (normalChainQuotient R P) ≤
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p K.goursatFst) := by
    apply Nat.le_of_mul_le_mul_right ?_ hRpos
    simpa only [Nat.mul_assoc] using hbudget
  have hpow := (Nat.mul_le_mul_left
    (p ^ Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA))
    (primeCharacters_pow_finrank_le_card p (normalChainQuotient R P))).trans hquot
  rw [← pow_add] at hpow
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpow

/-- Sharp relative-head bound, retaining the full radical contribution.
The rank increment is the actual extendible-character dimension. -/
theorem subdirectEvaluationAxis_relativeHead_le :
    letI := Subgroup.normal_goursatFst hA
    letI := subdirectEvaluationAxis_normal p K hA
    Module.finrank (ZMod p) (primeRelativeCharacters p (subdirectEvaluationAxis p K)) ≤
      (Module.finrank (ZMod p) (primeRelativeCharacters p K.goursatFst) -
        Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA)) +
      Module.finrank (ZMod p) (primeRelativeCharacters p
        (primeRelativeRadical p K.goursatFst)) := by
  letI := Subgroup.normal_goursatFst hA
  letI := subdirectEvaluationAxis_normal p K hA
  have h := primeRelativeHead_chain_le_absolute
    (primeRelativeRadical p K.goursatFst) (subdirectEvaluationAxis p K) p
    (subdirectRelativeRadical_le_evaluationAxis p K hA)
  have hq := subdirectEvaluationAxis_quotient_rank_bound p K hA
  omega

end SymmetricSubgroupAsymptotics
