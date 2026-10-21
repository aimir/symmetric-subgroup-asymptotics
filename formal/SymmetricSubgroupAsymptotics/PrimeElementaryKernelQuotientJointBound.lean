import SymmetricSubgroupAsymptotics.PrimeElementaryKernelQuotientDerived
import SymmetricSubgroupAsymptotics.PrimeElementaryKernelQuotientCenter
import SymmetricSubgroupAsymptotics.PGroupRankAdditivityRelativeRadical

/-! RDT5.6(ii)'s joint derived/centre estimate, with an integer exact
relative-head multiplier. The original ordinary rank-additivity premise
supplies radical equality internally. The image top and every quotient
map remain actual; no independent worst-case normal is substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
  {G B Q H : Type} [Group G] [Finite G] [Group B] [Finite B]
  [Group Q] [Finite Q] [Group H] [Finite H]

/-- Multiplying by the original relative-head price avoids a negative
exponent when stating the exact original-source inequality. -/
theorem pGroup_quotient_derived_center_joint_bound_of_rank_additivity
    (hG : IsPGroup p G) (beta : G →* B) (hbeta : Function.Surjective beta)
    (hpow : ∀ k : beta.ker, (k : G)^p=1)
    (hexp : ∀ a : Abelianization G, a^p=1)
    (hrank : MarkedC4.genRank G=MarkedC4.normalGen beta.ker+MarkedC4.genRank B)
    (q : G →* Q) (hq : Function.Surjective q) (hqker : q.ker≤commutator G)
    (d : ℕ) (hbound : ∀ (A : Subgroup G) [A.Normal],
      A≤beta.ker → MarkedC4.normalGen A≤d)
    (f : Q →* H) (hf : Function.Surjective f) (hfker : f.ker=beta.ker.map q) :
    p^MarkedC4.normalGen beta.ker *
        (Nat.card (commutator Q)*Nat.card (Subgroup.center Q)) ≤
      p^d*Nat.card (beta.ker.map q)*Nat.card (commutator H)*Nat.card (Subgroup.center H) := by
  have hR := pGroup_relativeRadical_eq_inf_commutator_of_rank_additivity
    p hG beta hbeta hpow hexp hrank
  have hd := pGroup_derived_card_kernel_image_identity p hG q hq beta.ker hR hqker f hf hfker
  have hz := pGroup_quotient_center_card_le_of_elementary_kernel_normalHead_bound
    p hG q hq beta.ker hpow d hbound f hf hfker
  calc
    _ = (p^MarkedC4.normalGen beta.ker*Nat.card (commutator Q))*
        Nat.card (Subgroup.center Q) := by ring
    _ = (Nat.card (beta.ker.map q)*Nat.card (commutator H))*
        Nat.card (Subgroup.center Q) := by rw [hd]
    _ ≤ (Nat.card (beta.ker.map q)*Nat.card (commutator H))*
        (p^d*Nat.card (Subgroup.center H)) := Nat.mul_le_mul_left _ hz
    _ = _ := by ring

end SymmetricSubgroupAsymptotics
