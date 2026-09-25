import SymmetricSubgroupAsymptotics.PrimeIndexCosetStep
import SymmetricSubgroupAsymptotics.MaximalNormalQuotient
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.OrderIsoNat

/-! Actual saturated subgroup chains in a finite p-group. Every cover
is normal inside its upper subgroup and has relative index p. The chain
starts at the original possibly nonnormal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- A cover in the original subgroup lattice is a maximal proper
subgroup after restriction to its actual upper group. -/
theorem subgroupCover_isCoatom (H K : Subgroup G) (hc : H ⋖ K) :
    IsCoatom (H.subgroupOf K) := by
  refine ⟨?_, ?_⟩
  · intro he
    exact (not_le_of_gt hc.lt) (Subgroup.subgroupOf_eq_top.mp he)
  · intro M hM
    have hlo : H ≤ M.map K.subtype := by
      have h := Subgroup.map_mono (f := K.subtype) hM.le
      rwa [Subgroup.map_subgroupOf_eq_of_le hc.le] at h
    rcases hc.eq_or_eq hlo (Subgroup.map_subtype_le M) with he | he
    · have hm : M = H.subgroupOf K := by
        apply Subgroup.map_injective K.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hc.le]
        exact he
      exact False.elim (hM.ne hm.symm)
    · apply Subgroup.map_injective K.subtype_injective
      simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

/-- Normality is local to the actual upper subgroup. -/
theorem pGroup_subgroupCover_normal [Finite G] (hG : IsPGroup p G)
    (H K : Subgroup G) (hc : H ⋖ K) : (H.subgroupOf K).Normal := by
  letI : Group.IsNilpotent K := (hG.to_subgroup K).isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom (H.subgroupOf K)
    (Group.normalizerCondition_of_isNilpotent (G := K)) (subgroupCover_isCoatom H K hc)

/-- A cover in a finite p-group has the literal relative index p. -/
theorem pGroup_subgroupCover_relIndex [Finite G] (hG : IsPGroup p G)
    (H K : Subgroup G) (hc : H ⋖ K) : H.relIndex K = p := by
  letI := pGroup_subgroupCover_normal hG H K hc
  have hmax := subgroupCover_isCoatom H K hc
  letI : IsSimpleGroup (K ⧸ H.subgroupOf K) :=
    maximal_normal_quotient_simple K (H.subgroupOf K) hmax.1 (by
      intro M hM hle
      rcases eq_or_lt_of_le hle with he | he
      · exact Or.inl he.symm
      · exact Or.inr (hmax.2 M he))
  have hQ : IsPGroup p (K ⧸ H.subgroupOf K) :=
    (hG.to_subgroup K).to_quotient (H.subgroupOf K)
  letI : Group.IsNilpotent (K ⧸ H.subgroupOf K) := hQ.isNilpotent
  have hprime : (Nat.card (K ⧸ H.subgroupOf K)).Prime := IsSimpleGroup.prime_card
  have hdvd : p ∣ Nat.card (K ⧸ H.subgroupOf K) :=
    hQ.card_eq_or_dvd.resolve_left hprime.ne_one
  have heq : p = Nat.card (K ⧸ H.subgroupOf K) :=
    ((Nat.dvd_prime hprime).mp hdvd).resolve_left (Fact.out : p.Prime).ne_one
  exact heq.symm

/-- A finite chain of literal ambient subgroups with normal prime-index
steps. Values beyond length are irrelevant and are never used. -/
structure PrimeIndexSubgroupChain (p : ℕ) (H L : Subgroup G) where
  length : ℕ
  subgroup : ℕ → Subgroup G
  first : subgroup 0 = H
  last : subgroup length = L
  step_le : ∀ i < length, subgroup i ≤ subgroup (i + 1)
  step_normal : ∀ i < length, ((subgroup i).subgroupOf (subgroup (i + 1))).Normal
  step_index : ∀ i < length, (subgroup i).relIndex (subgroup (i + 1)) = p

/-- No subnormal-chain assumption is added: the chain is constructed
in the finite lattice of the original p-group's subgroups. -/
theorem pGroup_primeIndexSubgroupChain_exists [Finite G] (hG : IsPGroup p G)
    (H L : Subgroup G) (hHL : H ≤ L) : Nonempty (PrimeIndexSubgroupChain p H L) := by
  obtain ⟨a, ha, n, han, hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le hHL
  exact ⟨{
    length := n
    subgroup := a
    first := ha
    last := han
    step_le := fun i hi => (hstep i hi).le
    step_normal := fun i hi => pGroup_subgroupCover_normal hG _ _ (hstep i hi)
    step_index := fun i hi => pGroup_subgroupCover_relIndex hG _ _ (hstep i hi) }⟩

/-- The length is controlled by the original relative index, not an
abstract replacement group or a selected regular subgroup. -/
theorem PrimeIndexSubgroupChain.relIndex {H L : Subgroup G}
    (s : PrimeIndexSubgroupChain p H L) : H.relIndex L = p ^ s.length := by
  have hlo : ∀ m ≤ s.length, H ≤ s.subgroup m := by
    intro m
    induction m with
    | zero => intro _; rw [s.first]
    | succ m ih =>
      intro hm
      exact (ih (by omega)).trans (s.step_le m (by omega))
  have hidx : ∀ m ≤ s.length, H.relIndex (s.subgroup m) = p ^ m := by
    intro m
    induction m with
    | zero => intro _; rw [s.first, Subgroup.relIndex_self, pow_zero]
    | succ m ih =>
      intro hm
      rw [← Subgroup.relIndex_mul_relIndex H (s.subgroup m) (s.subgroup (m + 1))
        (hlo m (by omega)) (s.step_le m (by omega)), ih (by omega),
        s.step_index m (by omega), pow_succ]
  simpa only [s.last] using hidx s.length le_rfl

theorem PrimeIndexSubgroupChain.length_eq {H L : Subgroup G}
    (s : PrimeIndexSubgroupChain p H L) {t : ℕ} (hindex : H.relIndex L = p ^ t) :
    s.length = t :=
  Nat.pow_right_injective (Fact.out : p.Prime).two_le (s.relIndex.symm.trans hindex)

end SymmetricSubgroupAsymptotics
