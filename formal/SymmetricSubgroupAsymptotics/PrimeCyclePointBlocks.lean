import SymmetricSubgroupAsymptotics.PrimePowerPointBlocks
import SymmetricSubgroupAsymptotics.CyclicBlockCentralizerProjection
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Prime.Pow

/-! A prime-index original block quotient is cyclic. Every outside element
therefore reaches the chosen original fibre by one of its integer powers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeCyclePointBlocks
open PermutationCharacterRankSplit

variable {G X : Type} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] {x₀ : X} {p r : ℕ}
    (D : PrimePowerPointBlock (A := G) x₀ p r)

def selected : SubMulAction D.subgroup X where
  carrier := {x | D.map x = D.base}
  smul_mem' a x hx := by
    change D.map ((a : G) • x) = D.base
    rw [D.map_equivariant,hx]
    change (a : G) • ((1 : G) : G ⧸ D.subgroup) = ((1 : G) : G ⧸ D.subgroup)
    rw [MulAction.Quotient.smul_coe]
    simpa only [smul_eq_mul,mul_one] using
      (QuotientGroup.eq.mpr (by simp) :
        ((a : G) : G ⧸ D.subgroup) = ((1 : G) : G ⧸ D.subgroup))

theorem selected_card : Nat.card (selected D) = p ^ r := D.base_fibre_card

theorem subgroup_index [Fact p.Prime]
    (hdegree : Nat.card X = p ^ (r + 1)) : D.subgroup.index = p := by
  have he := D.degree_product
  change p ^ r * D.subgroup.index = Nat.card X at he
  rw [hdegree,pow_succ] at he
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos r) he

omit [MulAction.IsPretransitive G X] in
theorem normal_of_prime_index [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (hi : D.subgroup.index = p) : D.subgroup.Normal := by
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  have hn : a ≠ 0 := by
    intro hz
    have hc := D.subgroup.card_mul_index
    rw [ha,hi,hz,pow_zero] at hc
    have hk := Nat.card_pos (α := D.subgroup)
    have hp := (Fact.out : p.Prime).two_le
    nlinarith
  apply D.subgroup.normal_of_index_eq_minFac_card
  rw [ha,(Fact.out : p.Prime).pow_minFac hn]
  exact hi

private theorem quotient_smul_eq_mul (K : Subgroup G) [K.Normal]
    (g : G) (q : G ⧸ K) : g • q = QuotientGroup.mk' K g * q := by
  induction q using Quotient.inductionOn with
  | h a => rfl

/-- The actual quotient, rather than a replacement cyclic action, supplies
reach of every original point into the selected original fibre. -/
theorem reach [Fact p.Prime] [Finite G] [D.subgroup.Normal]
    (hi : D.subgroup.index = p) (g : G) (hg : g ∉ D.subgroup) (x : X) :
    ∃ j : ℤ, (g^j) • x ∈ selected D := by
  let Q := G ⧸ D.subgroup
  let q : Q := QuotientGroup.mk' D.subgroup g
  have hq : q ≠ 1 := by
    intro he
    exact hg ((QuotientGroup.eq_one_iff g).mp he)
  letI : Fact (Nat.card Q).Prime := ⟨by
    change D.subgroup.index.Prime
    rw [hi]
    exact Fact.out⟩
  have hz : Subgroup.zpowers q = ⊤ := by
    rcases (Subgroup.zpowers q).eq_bot_or_eq_top_of_prime_card with he|he
    · have hm : q ∈ (⊥ : Subgroup Q) := he ▸ Subgroup.mem_zpowers q
      exact False.elim (hq (Subgroup.mem_bot.mp hm))
    · exact he
  have hm : (D.map x)⁻¹ ∈ Subgroup.zpowers q := by rw [hz]; trivial
  obtain ⟨j,hj⟩ := Subgroup.mem_zpowers_iff.mp hm
  refine ⟨j,?_⟩
  change D.map ((g^j) • x) = D.base
  rw [D.map_equivariant,quotient_smul_eq_mul]
  change (QuotientGroup.mk' D.subgroup (g^j)) * D.map x = 1
  rw [map_zpow]
  change q^j * D.map x = 1
  rw [hj,inv_mul_cancel]

variable [Finite X]

theorem complement_card [Fact p.Prime] (hdegree : Nat.card X = p ^ (r + 1)) :
    Nat.card ↥((selected D)ᶜ) = (p-1) * p ^ r := by
  have hs := card_split (selected D)
  rw [selected_card D,hdegree,pow_succ] at hs
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hscaled := congrArg (fun z : ℕ => z * p ^ r) hpred
  nlinarith

end SymmetricSubgroupAsymptotics.PrimeCyclePointBlocks
