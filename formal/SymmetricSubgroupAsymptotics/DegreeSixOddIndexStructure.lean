import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.CoprimeOrbitLabels
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The literal ternary base of a degree-six odd-index-two owner

Let `U` act faithfully and transitively on six points with a normal ternary
subgroup `T` of index two.  Then `T` is abelian of exponent three and has
order three or nine.  A point stabilizer lies in `T`; if an element outside
`T` normalized it, the stabilizer would be normal and hence trivial, which
is impossible when `|T| = 9`.  This yields a ternary character of `T`, with
kernel the stabilizer, which detects every nonidentity element together with
its conjugate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C1OddIndexTwoOwnerWitness

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (W : C1OddIndexTwoOwnerWitness U)

theorem ternary_normal' : W.ternary.Normal := W.normal

theorem quotient_card : Nat.card (U ⧸ W.ternary) = 2 := W.index_two

theorem ternary_card_mul_two : Nat.card W.ternary * 2 = Nat.card U := by
  rw [← W.index_two]
  exact W.ternary.card_mul_index

theorem sq_mem (x : U) : x ^ 2 ∈ W.ternary := by
  letI := W.normal
  have h : (QuotientGroup.mk x : U ⧸ W.ternary) ^ 2 = 1 := by
    rw [← W.quotient_card]
    exact pow_card_eq_one'
  rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h

theorem exists_not_mem : ∃ s : U, s ∉ W.ternary := by
  by_contra h
  push_neg at h
  have htop : W.ternary = ⊤ := eq_top_iff.mpr fun x _ => h x
  have hidx := W.index_two
  rw [htop, Subgroup.index_top] at hidx
  omega

theorem mem_or_inv_mul_mem {s : U} (hs : s ∉ W.ternary) (x : U) :
    x ∈ W.ternary ∨ s⁻¹ * x ∈ W.ternary := by
  letI := W.normal
  letI : Fintype (U ⧸ W.ternary) := Fintype.ofFinite _
  exact mem_or_inv_mul_mem_of_index_two W.ternary hs W.quotient_card x

variable [MulAction.IsPretransitive U X]

theorem six_dvd_card (hX : Nat.card X = 6) : 6 ∣ Nat.card U := by
  have hne : Nonempty X := (Nat.card_pos_iff.mp (by rw [hX]; norm_num)).1
  obtain ⟨x0⟩ := hne
  have hidx := MulAction.index_stabilizer_of_transitive U x0
  rw [hX] at hidx
  rw [← hidx]
  exact Subgroup.index_dvd_card _

theorem ternary_card (hX : Nat.card X = 6) :
    Nat.card W.ternary = 3 ∨ Nat.card W.ternary = 9 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp W.ternaryPGroup
  have h6 := six_dvd_card (U := U) hX
  have hU := W.ternary_card_mul_two
  have hperm : Nat.card U ∣ 720 := by
    have h := Subgroup.card_subgroup_dvd_card U
    rwa [Nat.card_perm, hX] at h
  rw [← hU, hk] at h6 hperm
  have hle : 3 ^ k * 2 ≤ 720 := Nat.le_of_dvd (by norm_num) hperm
  have hk6 : k < 6 := by
    by_contra h
    have : 3 ^ 6 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk]
  interval_cases k
  all_goals (revert h6 hperm; decide)

theorem ternary_comm (hX : Nat.card X = 6) :
    ∀ a b : W.ternary, a * b = b * a := by
  rcases W.ternary_card hX with h3 | h9
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsCyclic W.ternary := isCyclic_of_prime_card h3
    obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := W.ternary)
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hz a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hz b)
    exact (Commute.zpow_zpow_self z i j).eq
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [h9]; norm_num)

private theorem dvd_three_of_dvd_nine_of_le_six {n : ℕ} (h9 : n ∣ 9) (h6 : n ≤ 6) : n ∣ 3 := by
  have : n ≤ 9 := Nat.le_of_dvd (by norm_num) h9
  interval_cases n <;> simp_all

theorem ternary_pow_three (hX : Nat.card X = 6) (t : W.ternary) : t ^ 3 = 1 := by
  rcases W.ternary_card hX with h3 | h9
  · rw [← h3]
    exact pow_card_eq_one'
  · letI : Fintype X := Fintype.ofFinite X
    have ht9 : t ^ 9 = 1 := by
      rw [← h9]
      exact pow_card_eq_one'
    let g : Equiv.Perm X := ((t : U) : Equiv.Perm X)
    have hg9 : g ^ 9 = 1 := by
      have := congrArg (fun z : W.ternary => ((z : U) : Equiv.Perm X)) ht9
      simpa [g] using this
    have hord : orderOf g ∣ 9 := orderOf_dvd_of_pow_eq_one hg9
    have hlcm : g.cycleType.lcm ∣ 3 := by
      apply Multiset.lcm_dvd.mpr
      intro n hn
      apply dvd_three_of_dvd_nine_of_le_six
      · exact (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
      · have h1 := Equiv.Perm.le_card_support_of_mem_cycleType hn
        have h2 : g.support.card ≤ Fintype.card X := Finset.card_le_univ _
        rw [Fintype.card_eq_nat_card, hX] at h2
        omega
    rw [Equiv.Perm.lcm_cycleType] at hlcm
    have hg3 : g ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hlcm
    apply Subtype.ext
    apply Subtype.ext
    simpa [g] using hg3

/-- A point stabilizer is never normalized by an element outside a ternary
base of order nine. -/
theorem stabilizer_not_normalized (hX : Nat.card X = 6)
    (hT9 : Nat.card W.ternary = 9) (s : U) (hs : s ∉ W.ternary) (x0 : X)
    (hnorm : ∀ u ∈ MulAction.stabilizer U x0,
      s * u * s⁻¹ ∈ MulAction.stabilizer U x0) : False := by
  let S := MulAction.stabilizer U x0
  have hUcard : Nat.card U = 18 := by
    rw [← W.ternary_card_mul_two, hT9]
  have hScard : Nat.card S = 3 := by
    have hidx := MulAction.index_stabilizer_of_transitive U x0
    rw [hX] at hidx
    have hmul := S.card_mul_index
    rw [hidx, hUcard] at hmul
    omega
  have hST : ∀ u ∈ S, u ∈ W.ternary := by
    intro u hu
    have hu3 : u ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := S) (x := ⟨u, hu⟩)
      rw [hScard] at h
      exact congrArg Subtype.val h
    have hu : u = (u ^ 2)⁻¹ := by
      calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
        _ = (u ^ 2)⁻¹ := by rw [hu3, one_mul]
    rw [hu]
    exact W.ternary.inv_mem (W.sq_mem u)
  have hcomm := W.ternary_comm hX
  have hnormal : ∀ g : U, ∀ u ∈ S, g * u * g⁻¹ ∈ S := by
    intro g u hu
    have huT := hST u hu
    rcases W.mem_or_inv_mul_mem hs g with hg | hg
    · have hc := congrArg Subtype.val (hcomm ⟨g, hg⟩ ⟨u, huT⟩)
      simp only [Subgroup.coe_mul] at hc
      rw [hc, mul_inv_cancel_right]
      exact hu
    · have hc := congrArg Subtype.val (hcomm ⟨s⁻¹ * g, hg⟩ ⟨u, huT⟩)
      simp only [Subgroup.coe_mul] at hc
      have hgu : g * u * g⁻¹ = s * u * s⁻¹ := by
        calc g * u * g⁻¹ = s * ((s⁻¹ * g) * u) * (s⁻¹ * g)⁻¹ * s⁻¹ := by group
          _ = s * (u * (s⁻¹ * g)) * (s⁻¹ * g)⁻¹ * s⁻¹ := by rw [hc]
          _ = s * u * s⁻¹ := by group
      rw [hgu]
      exact hnorm u hu
  have htriv : ∀ u ∈ S, u = 1 := by
    intro u hu
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq U x0 y
    have hc : h⁻¹ * u * h ∈ S := by
      have := hnormal h⁻¹ u hu
      simpa using this
    have hfix : (h⁻¹ * u * h) • x0 = x0 := hc
    have : u • (h • x0) = h • x0 := by
      calc u • (h • x0) = h • ((h⁻¹ * u * h) • x0) := by
            rw [← mul_smul, ← mul_smul]
            congr 1
            group
        _ = h • x0 := by rw [hfix]
    exact this
  have hbot : S = ⊥ := eq_bot_iff.mpr fun u hu => Subgroup.mem_bot.mpr (htriv u hu)
  have h1 : Nat.card S = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  omega

/-- Conjugation by an element outside a ternary base of order nine is
neither trivial nor inversion on the base. -/
theorem conj_not_trivial (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9)
    (s : U) (hs : s ∉ W.ternary) :
    ∃ v : W.ternary, (letI := W.normal; MulAut.conjNormal s v) ≠ v := by
  letI := W.normal
  by_contra h
  push Not at h
  have hne : Nonempty X := (Nat.card_pos_iff.mp (by rw [hX]; norm_num)).1
  obtain ⟨x0⟩ := hne
  apply W.stabilizer_not_normalized hX hT9 s hs x0
  intro u hu
  -- The stabilizer lies in the base, so conjugation fixes it.
  have huT : u ∈ W.ternary := by
    have hScard : Nat.card (MulAction.stabilizer U x0) = 3 := by
      have hidx := MulAction.index_stabilizer_of_transitive U x0
      rw [hX] at hidx
      have hmul := (MulAction.stabilizer U x0).card_mul_index
      rw [hidx, ← W.ternary_card_mul_two, hT9] at hmul
      omega
    have hu3 : u ^ 3 = 1 := by
      have h' := pow_card_eq_one' (G := MulAction.stabilizer U x0) (x := ⟨u, hu⟩)
      rw [hScard] at h'
      exact congrArg Subtype.val h'
    have : u = (u ^ 2)⁻¹ := by
      calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
        _ = (u ^ 2)⁻¹ := by rw [hu3, one_mul]
    rw [this]
    exact W.ternary.inv_mem (W.sq_mem u)
  have hfix := congrArg Subtype.val (h ⟨u, huT⟩)
  simp only [MulAut.conjNormal_apply] at hfix
  rw [hfix]
  exact hu


theorem stabilizer_card (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9) (x0 : X) :
    Nat.card (MulAction.stabilizer U x0) = 3 := by
  have hidx := MulAction.index_stabilizer_of_transitive U x0
  rw [hX] at hidx
  have hmul := (MulAction.stabilizer U x0).card_mul_index
  rw [hidx, ← W.ternary_card_mul_two, hT9] at hmul
  omega

theorem stabilizer_le (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9) (x0 : X) :
    MulAction.stabilizer U x0 ≤ W.ternary := by
  intro u hu
  have hu3 : u ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := MulAction.stabilizer U x0) (x := ⟨u, hu⟩)
    rw [W.stabilizer_card hX hT9 x0] at h
    exact congrArg Subtype.val h
  have : u = (u ^ 2)⁻¹ := by
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = (u ^ 2)⁻¹ := by rw [hu3, one_mul]
  rw [this]
  exact W.ternary.inv_mem (W.sq_mem u)

/-- The stabilizer, viewed inside the ternary base. -/
def stabilizerKernel (x0 : X) : Subgroup W.ternary :=
  (MulAction.stabilizer U x0).subgroupOf W.ternary

theorem stabilizerKernel_normal (hX : Nat.card X = 6) (x0 : X) :
    (W.stabilizerKernel x0).Normal where
  conj_mem n hn g := by
    rw [W.ternary_comm hX g n, mul_inv_cancel_right]
    exact hn

theorem stabilizerKernel_card (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9) (x0 : X) :
    Nat.card (W.stabilizerKernel x0) = 3 := by
  rw [stabilizerKernel, ← W.stabilizer_card hX hT9 x0]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (W.stabilizer_le hX hT9 x0)).toEquiv

theorem stabilizerQuotient_card (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9)
    (x0 : X) :
    letI := W.stabilizerKernel_normal hX x0
    Nat.card (W.ternary ⧸ W.stabilizerKernel x0) = 3 := by
  have hmul := (W.stabilizerKernel x0).card_mul_index
  rw [W.stabilizerKernel_card hX hT9 x0, hT9] at hmul
  change 3 * Nat.card (W.ternary ⧸ W.stabilizerKernel x0) = 9 at hmul
  omega

/-- The ternary character of the base whose kernel is the literal stabilizer. -/
def stabilizerCharacter (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9) (x0 : X) :
    W.ternary →* Multiplicative (ZMod 3) :=
  letI := W.stabilizerKernel_normal hX x0
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  (mulEquivOfPrimeCardEq (W.stabilizerQuotient_card hX hT9 x0)
    (by rw [Nat.card_eq_fintype_card]; rfl)).toMonoidHom.comp
    (QuotientGroup.mk' (W.stabilizerKernel x0))

theorem stabilizerCharacter_eq_one_iff (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9)
    (x0 : X) (t : W.ternary) :
    W.stabilizerCharacter hX hT9 x0 t = 1 ↔ (t : U) ∈ MulAction.stabilizer U x0 := by
  letI := W.stabilizerKernel_normal hX x0
  unfold stabilizerCharacter
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl

/-- The stabilizer character detects every nonidentity base element
together with its conjugate by any element outside the base. -/
theorem stabilizerCharacter_pair (hX : Nat.card X = 6) (hT9 : Nat.card W.ternary = 9)
    (x0 : X) (s : U) (hs : s ∉ W.ternary) (t : W.ternary)
    (h1 : W.stabilizerCharacter hX hT9 x0 t = 1)
    (h2 : W.stabilizerCharacter hX hT9 x0 (letI := W.normal; MulAut.conjNormal s t) = 1) :
    t = 1 := by
  letI := W.normal
  rw [stabilizerCharacter_eq_one_iff] at h1 h2
  simp only [MulAut.conjNormal_apply] at h2
  by_contra ht
  apply W.stabilizer_not_normalized hX hT9 s hs x0
  intro u hu
  -- The stabilizer has prime order, so it is generated by the nonidentity t.
  have htne : (t : U) ≠ 1 := by
    intro h
    exact ht (Subtype.ext h)
  have ht3 : (t : U) ^ 3 = 1 := congrArg Subtype.val (W.ternary_pow_three hX t)
  have hord : orderOf (t : U) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime ht3 htne
  have hle : Subgroup.zpowers (t : U) ≤ MulAction.stabilizer U x0 :=
    (Subgroup.zpowers_le).mpr h1
  have heq : Subgroup.zpowers (t : U) = MulAction.stabilizer U x0 := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [W.stabilizer_card hX hT9 x0, Nat.card_zpowers, hord]
  rw [← heq] at hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hconj : s * (t : U) ^ k * s⁻¹ = (s * (t : U) * s⁻¹) ^ k := by
    rw [conj_zpow]
  rw [hconj]
  exact (MulAction.stabilizer U x0).zpow_mem h2 k

end C1OddIndexTwoOwnerWitness
end SymmetricSubgroupAsymptotics

end
