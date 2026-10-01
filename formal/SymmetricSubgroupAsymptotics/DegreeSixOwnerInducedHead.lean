import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.DegreeSixOddIndexStructure
import SymmetricSubgroupAsymptotics.InducedElementHead
import SymmetricSubgroupAsymptotics.InducedTernaryHead
import SymmetricSubgroupAsymptotics.PGroupInducedHead
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.RepresentationTheory.Invariants

/-!
# Degree-six owner bounds for one-dimensional induced layers

The exceptional width-six induced coefficient is sharpened on the two
intrinsic high-head owners.  An odd-index-two ternary owner with a nonzero
relative ternary head contains a literal six-cycle.  A cyclic binary owner
is treated by averaging over its normal binary base; the invariant part
embeds in the regular module of its ternary complement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics

section NormalInvariants

variable {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]

/-- Restrict an invariant linear form to the invariants of a normal
subgroup. -/
def representationHeadRestrictNormalInvariants
    (ρ : Representation k G V) (B : Subgroup G) [B.Normal] :
    ρ.IntertwiningMap (Representation.trivial k G k) →ₗ[k]
      (Representation.toInvariants ρ B).IntertwiningMap
        (Representation.trivial k G k) where
  toFun f := {
    toLinearMap := f.toLinearMap.comp (Representation.invariants (ρ.comp B.subtype)).subtype
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      exact Representation.IntertwiningMap.isIntertwining ρ
        (Representation.trivial k G k) f g v.1 }
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl

/-- In coprime characteristic an invariant form is determined by its
restriction to the normal-subgroup invariants. -/
theorem representationHeadRestrictNormalInvariants_injective
    (ρ : Representation k G V) (B : Subgroup G) [B.Normal]
    [Fintype B] [Invertible (Fintype.card B : k)] :
    Function.Injective (representationHeadRestrictNormalInvariants ρ B) := by
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  let ρB : Representation k B V := ρ.comp B.subtype
  let av : Representation.invariants ρB :=
    ⟨Representation.averageMap ρB v, Representation.averageMap_invariant ρB v⟩
  have hav := congrArg
    (fun q : (Representation.toInvariants ρ B).IntertwiningMap
      (Representation.trivial k G k) => q av) hfg
  change f (Representation.averageMap ρB v) =
    g (Representation.averageMap ρB v) at hav
  have hf : f (Representation.averageMap ρB v) = f v := by
    have hfB (x : B) : f (ρB x v) = f v := by
      simpa using Representation.IntertwiningMap.isIntertwining ρ
        (Representation.trivial k G k) f x.1 v
    simp [Representation.averageMap, GroupAlgebra.average, hfB,
      Finset.card_univ, Invertible.ne_zero]
  have hg : g (Representation.averageMap ρB v) = g v := by
    have hgB (x : B) : g (ρB x v) = g v := by
      simpa using Representation.IntertwiningMap.isIntertwining ρ
        (Representation.trivial k G k) g x.1 v
    simp [Representation.averageMap, GroupAlgebra.average, hgB,
      Finset.card_univ, Invertible.ne_zero]
  exact hf.symm.trans (hav.trans hg)

/-- The complete head is bounded by the head on the invariants of a normal
coprime subgroup. -/
theorem representationHead_le_normalInvariants
    [FiniteDimensional k V]
    (ρ : Representation k G V) (B : Subgroup G) [B.Normal]
    [Fintype B] [Invertible (Fintype.card B : k)] :
    Module.finrank k
      (ρ.IntertwiningMap (Representation.trivial k G k)) ≤
    Module.finrank k
      ((Representation.toInvariants ρ B).IntertwiningMap
        (Representation.trivial k G k)) :=
  (representationHeadRestrictNormalInvariants ρ B).finrank_le_finrank_of_injective
    (representationHeadRestrictNormalInvariants_injective ρ B)

end NormalInvariants

section CyclicQuotientStabilizer

variable {G X : Type} [Group G] [MulAction G X]

/-- A cyclic subgroup which is transitive on the point set is also
transitive on the cosets of a point stabilizer.  This is the precise
bridge needed by the function-model estimate for induced modules. -/
theorem cyclicQuotientStabilizer_pretransitive
    (g : G) [MulAction.IsPretransitive (Subgroup.zpowers g) X] (x : X) :
    MulAction.IsPretransitive (Subgroup.zpowers g)
      (G ⧸ MulAction.stabilizer G x) := by
  constructor
  intro q₁ q₂
  induction q₁ using Quotient.inductionOn' with
  | _ a =>
      induction q₂ using Quotient.inductionOn' with
      | _ b =>
          obtain ⟨z, hz⟩ := MulAction.exists_smul_eq
            (Subgroup.zpowers g) (a • x) (b • x)
          refine ⟨z, ?_⟩
          apply MulAction.injective_ofQuotientStabilizer G x
          change ((z : G) * a) • x = b • x
          simpa only [mul_smul] using hz

end CyclicQuotientStabilizer

namespace C1OddIndexTwoOwnerWitness

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (W : C1OddIndexTwoOwnerWitness U)

/-- Schur--Zassenhaus supplies the literal involutory complement to the
normal ternary base. -/
theorem complement_exists :
    ∃ P : Subgroup U, Subgroup.IsComplement' W.ternary P := by
  letI := W.normal
  obtain ⟨n, hn⟩ := W.ternaryPGroup.exists_card_eq
  apply Subgroup.exists_right_complement'_of_coprime
  rw [hn, W.index_two]
  exact Nat.Coprime.pow_left n (by decide)

theorem complement_card (P : Subgroup U)
    (hP : Subgroup.IsComplement' W.ternary P) : Nat.card P = 2 := by
  have hbase := W.ternary.card_mul_index
  rw [W.index_two] at hbase
  have hcomp := hP.card_mul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcomp.trans hbase.symm)

/-- If an element outside the ternary base acts by inversion on that base,
then every ambient-invariant ternary character of every normal subgroup is
zero.  Squaring first moves an arbitrary element into the base, so no
splitting of the normal subgroup is required. -/
theorem relativeHead_eq_zero_of_inversion
    (M : Subgroup U) [M.Normal]
    (s : U) (_hs : s ∉ W.ternary)
    (hinv : ∀ t : W.ternary,
      normalConjugate W.ternary W.normal t s = t⁻¹) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 0 := by
  have hzero (η : primeRelativeCharacters 3 M) (m : M) :
      η.1 (Additive.ofMul m) = 0 := by
    let mt : M := m ^ 2
    let t : W.ternary := ⟨(m : U) ^ 2, W.sq_mem (m : U)⟩
    have hconj : s * (mt : U) * s⁻¹ = ((mt : U))⁻¹ := by
      exact congrArg Subtype.val (hinv t)
    have hηinv := η.2 s mt
    change η.1 (Additive.ofMul
        (⟨s * (mt : U) * s⁻¹,
          Subgroup.Normal.conj_mem inferInstance _ mt.2 s⟩ : M)) =
      η.1 (Additive.ofMul mt) at hηinv
    have hmtinv :
        (⟨s * (mt : U) * s⁻¹,
          Subgroup.Normal.conj_mem inferInstance _ mt.2 s⟩ : M) = mt⁻¹ := by
      apply Subtype.ext
      exact hconj
    rw [hmtinv] at hηinv
    have hneg : η.1 (Additive.ofMul mt⁻¹) =
        -η.1 (Additive.ofMul mt) := by
      simpa using η.1.map_neg (Additive.ofMul mt)
    rw [hneg] at hηinv
    have hmtzero : η.1 (Additive.ofMul mt) = 0 := by
      have htwo : (2 : ZMod 3) * η.1 (Additive.ofMul mt) = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp hηinv.symm
      exact (mul_eq_zero.mp htwo).resolve_left (by decide)
    have hsquare : η.1 (Additive.ofMul mt) =
        η.1 (Additive.ofMul m) + η.1 (Additive.ofMul m) := by
      have hmt : mt = m * m := by
        apply Subtype.ext
        simp [mt, pow_two]
      rw [hmt]
      exact η.1.map_add (Additive.ofMul m) (Additive.ofMul m)
    have htwo : (2 : ZMod 3) * η.1 (Additive.ofMul m) = 0 := by
      rw [two_mul, ← hsquare, hmtzero]
    exact (mul_eq_zero.mp htwo).resolve_left (by decide)
  have hsub : Subsingleton (primeRelativeCharacters 3 M) := by
    constructor
    intro χ ψ
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro m
    change χ.1 (Additive.ofMul m.toMul) = ψ.1 (Additive.ofMul m.toMul)
    rw [hzero χ m.toMul, hzero ψ m.toMul]
  letI := hsub
  exact Module.finrank_zero_of_subsingleton

/-- A literal complement generator has order two and lies outside the
ternary base. -/
theorem exists_complement_involution :
    ∃ (P : Subgroup U) (s : P),
      Subgroup.IsComplement' W.ternary P ∧ s ≠ 1 ∧
        ((s : U) ^ 2 = 1) ∧ (s : U) ∉ W.ternary := by
  obtain ⟨P, hP⟩ := W.complement_exists
  have hPcard := W.complement_card P hP
  letI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨s, hs⟩ := exists_ne (1 : P)
  have hs2 : (s : P) ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := P) (x := s)
    rwa [hPcard] at h
  have hsT : (s : U) ∉ W.ternary := by
    intro hsT
    have hbot : (s : U) ∈ (⊥ : Subgroup U) :=
      hP.disjoint.le_bot ⟨hsT, s.2⟩
    exact hs (Subtype.ext (Subgroup.mem_bot.mp hbot))
  exact ⟨P, s, hP, hs, congrArg Subtype.val hs2, hsT⟩

/-- A nonzero relative head rules out inversion by the complement.  The
resulting norm element is nontrivial and central in the whole degree-six
group. -/
theorem exists_nontrivial_central_ternary
    [MulAction.IsPretransitive U X]
    (hX : Nat.card X = 6)
    (M : Subgroup U) [M.Normal]
    (hM : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) ≠ 0) :
    ∃ v : W.ternary, v ≠ 1 ∧ (v : U) ∈ Subgroup.center U := by
  obtain ⟨P, s, hP, hs, hs2, hsT⟩ := W.exists_complement_involution
  have hnotinv : ¬ ∀ t : W.ternary,
      normalConjugate W.ternary W.normal t (s : U) = t⁻¹ := by
    intro hinv
    exact hM (W.relativeHead_eq_zero_of_inversion M (s : U) hsT hinv)
  push_neg at hnotinv
  obtain ⟨t, ht⟩ := hnotinv
  let αt : W.ternary := normalConjugate W.ternary W.normal t (s : U)
  let v : W.ternary := t * αt
  have hvne : v ≠ 1 := by
    intro hv
    apply ht
    apply eq_inv_of_mul_eq_one_right
    exact hv
  have hsinv : ((s : U) : U)⁻¹ = (s : U) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hs2
  have hαfix : normalConjugate W.ternary W.normal v (s : U) = v := by
    apply Subtype.ext
    have hcomm := congrArg Subtype.val (W.ternary_comm hX t αt)
    simp only [Subgroup.coe_mul] at hcomm
    have hss : (s : U) * (s : U) = 1 := by
      simpa only [pow_two] using hs2
    have hαα : (s : U) * (αt : U) * (s : U) = (t : U) := by
      simp only [αt, normalConjugate_coe, hsinv]
      calc
        (s : U) * ((s : U) * (t : U) * (s : U)) * (s : U) =
            ((s : U) * (s : U)) * (t : U) * ((s : U) * (s : U)) := by group
        _ = (t : U) := by rw [hss]; simp
    have hαt : (αt : U) = (s : U) * (t : U) * (s : U) := by
      simp only [αt, normalConjugate_coe, hsinv]
    simp only [normalConjugate_coe, v, Subgroup.coe_mul, hsinv]
    calc
      (s : U) * ((t : U) * (αt : U)) * (s : U) =
          ((s : U) * (t : U) * (s : U)) *
            ((s : U) * (αt : U) * (s : U)) := by
              calc
                _ = (s : U) * (t : U) *
                    (1 * (αt : U)) * (s : U) := by simp [mul_assoc]
                _ = (s : U) * (t : U) *
                    (((s : U) * (s : U)) * (αt : U)) * (s : U) := by rw [hss]
                _ = _ := by group
      _ = (αt : U) * (t : U) := by
        rw [hαα, hαt]
      _ = (t : U) * (αt : U) := hcomm.symm
  have hPcard := W.complement_card P hP
  have hsord : orderOf s = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by exact_mod_cast hs2) hs
  have hPgen : Subgroup.zpowers s = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Nat.card_zpowers, hsord, Subgroup.card_top, hPcard]
  have hvcommP : ∀ p : P, Commute (v : U) (p : U) := by
    intro p
    have hp : p ∈ Subgroup.zpowers s := by
      rw [hPgen]
      exact Subgroup.mem_top p
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hvs : Commute (v : U) (s : U) := by
      have hc := congrArg Subtype.val hαfix
      simp only [normalConjugate_coe, hsinv] at hc
      have hss : (s : U) * (s : U) = 1 := by
        simpa only [pow_two] using hs2
      have hleft := congrArg (fun z : U => (s : U) * z) hc
      show (v : U) * (s : U) = (s : U) * (v : U)
      simpa only [← mul_assoc, hss, one_mul] using hleft
    have := hvs.zpow_right n
    have hnU : (s : U) ^ n = (p : U) := congrArg Subtype.val hn
    rw [← hnU]
    exact this
  have hvcenter : (v : U) ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨⟨a, p⟩, hap⟩ := hP.2 u
    have hva : Commute (v : U) (a : U) := by
      show (v : U) * (a : U) = (a : U) * (v : U)
      exact congrArg Subtype.val (W.ternary_comm hX v a)
    have hvp := hvcommP p
    have hprod := hva.mul_right hvp
    change (a : U) * (p : U) = u at hap
    rw [← hap]
    exact hprod.eq.symm
  exact ⟨v, hvne, hvcenter⟩

theorem stabilizer_le_ternary
    [MulAction.IsPretransitive U X]
    (hX : Nat.card X = 6) (x : X) :
    MulAction.stabilizer U x ≤ W.ternary := by
  rcases W.ternary_card hX with h3 | h9
  · let S := MulAction.stabilizer U x
    have hU : Nat.card U = 6 := by
      rw [← W.ternary_card_mul_two, h3]
    have hindex : S.index = 6 := by
      simpa only [S, hX] using MulAction.index_stabilizer_of_transitive U x
    have hcard : Nat.card S = 1 := by
      have hmul := S.card_mul_index
      rw [hindex, hU] at hmul
      omega
    letI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hcard).1
    intro u hu
    let us : S := ⟨u, hu⟩
    have hus : us = 1 := Subsingleton.elim _ _
    have hu1 : u = 1 := congrArg Subtype.val hus
    rw [hu1]
    exact W.ternary.one_mem
  · exact W.stabilizer_le hX h9 x

/-- In a faithful transitive permutation group, a central element fixing
one point is the identity. -/
theorem eq_one_of_mem_center_of_fixed
    [MulAction.IsPretransitive U X]
    (z : U) (hz : z ∈ Subgroup.center U) (x : X)
    (hfix : z • x = x) : z = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨u, rfl⟩ := MulAction.exists_smul_eq U x y
  have hc := Subgroup.mem_center_iff.mp hz u
  change (z : Equiv.Perm X) ((u : Equiv.Perm X) x) = (u : Equiv.Perm X) x
  have hc' := congrArg (fun q : U => ((q : Equiv.Perm X) x)) hc.symm
  calc
    (z : Equiv.Perm X) ((u : Equiv.Perm X) x) =
        (u : Equiv.Perm X) ((z : Equiv.Perm X) x) := by
          simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply] using hc'
    _ = (u : Equiv.Perm X) x := congrArg (fun q : X => (u : Equiv.Perm X) q) hfix

include W in
/-- A nonzero relative head in an odd-index-two owner produces an actual
six-cycle in the original degree-six action. -/
theorem exists_six_cycle_of_relativeHead_ne_zero
    [MulAction.IsPretransitive U X]
    (hX : Nat.card X = 6)
    (M : Subgroup U) [M.Normal]
    (hM : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) ≠ 0) :
    ∃ g : U, MulAction.IsPretransitive (Subgroup.zpowers g) X := by
  obtain ⟨v, hvne, hvcenter⟩ :=
    C1OddIndexTwoOwnerWitness.exists_nontrivial_central_ternary W hX M hM
  obtain ⟨P, s, _hP, hs, hs2, _hsT⟩ := W.exists_complement_involution
  have hv3U : (v : U) ^ 3 = 1 := congrArg Subtype.val (W.ternary_pow_three hX v)
  have hvneU : (v : U) ≠ 1 := by
    intro h
    exact hvne (Subtype.ext h)
  have hvord : orderOf (v : U) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hv3U hvneU
  have hsneU : (s : U) ≠ 1 := by
    intro h
    exact hs (Subtype.ext h)
  have hsord : orderOf (s : U) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact orderOf_eq_prime hs2 hsneU
  have hcomm : Commute (v : U) (s : U) := by
    have hc := Subgroup.mem_center_iff.mp hvcenter (s : U)
    exact hc.symm
  let g : U := (v : U) * (s : U)
  have hg2 : g ^ 2 = (v : U) ^ 2 := by
    dsimp only [g]
    rw [hcomm.mul_pow, hs2, mul_one]
  have hg3 : g ^ 3 = (s : U) := by
    dsimp only [g]
    rw [hcomm.mul_pow, hv3U, one_mul]
    calc
      (s : U) ^ 3 = (s : U) ^ 2 * (s : U) := by rw [pow_succ]
      _ = (s : U) := by rw [hs2, one_mul]
  have hg6 : g ^ 6 = 1 := by
    dsimp only [g]
    rw [hcomm.mul_pow]
    have hv6 : (v : U) ^ 6 = 1 := by
      rw [show 6 = 3 * 2 by norm_num, pow_mul, hv3U, one_pow]
    have hs6 : (s : U) ^ 6 = 1 := by
      rw [show 6 = 2 * 3 by norm_num, pow_mul, hs2, one_pow]
    rw [hv6, hs6, mul_one]
  have hgord : orderOf g = 6 := by
    have hdvd : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one hg6
    have hle : orderOf g ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf g := orderOf_pos g
    interval_cases h : orderOf g
    · have : g = 1 := orderOf_eq_one_iff.mp h
      rw [this, one_pow] at hg3
      exact (hsneU hg3.symm).elim
    · have hpow : g ^ 2 = 1 := by
        rw [← h]
        exact pow_orderOf_eq_one g
      rw [hg2] at hpow
      have hvordDvd : orderOf (v : U) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
      rw [hvord] at hvordDvd
      norm_num at hvordDvd
    · have hpow : g ^ 3 = 1 := by
        rw [← h]
        exact pow_orderOf_eq_one g
      rw [hg3] at hpow
      exact (hsneU hpow).elim
    · norm_num at hdvd
    · norm_num at hdvd
    · rfl
  have hpre : MulAction.IsPretransitive (Subgroup.zpowers g) X := by
    constructor
    intro x y
    have hstab : MulAction.stabilizer (Subgroup.zpowers g) x = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have haT : (a : U) ∈ W.ternary := by
        apply W.stabilizer_le_ternary hX x
        change (a : U) • x = x
        exact ha
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have haU : (a : U) = g ^ n := hn.symm
      have hg2center : g ^ 2 ∈ Subgroup.center U := by
        rw [hg2]
        exact (Subgroup.center U).pow_mem hvcenter 2
      have ha2center : (a : U) ^ 2 ∈ Subgroup.center U := by
        have heq : (a : U) ^ 2 = (g ^ 2) ^ n := by
          rw [haU]
          simp only [← zpow_natCast, ← zpow_mul]
          congr 1
          omega
        rw [heq]
        exact (Subgroup.center U).zpow_mem hg2center n
      have ha2fix : ((a : U) ^ 2) • x = x := by
        have hafix := ha
        change (a : U) • x = x at hafix
        change (a : U) • ((a : U) • x) = x
        rw [hafix, hafix]
      have ha2 : (a : U) ^ 2 = 1 :=
        eq_one_of_mem_center_of_fixed ((a : U) ^ 2) ha2center x ha2fix
      let av : W.ternary := ⟨(a : U), haT⟩
      have ha3 : (a : U) ^ 3 = 1 := congrArg Subtype.val (W.ternary_pow_three hX av)
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      calc
        (a : U) = (a : U) ^ 3 * ((a : U) ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, ha2]; simp
    have horbit : MulAction.orbit (Subgroup.zpowers g) x = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [Set.ncard_univ, hX, ← MulAction.index_stabilizer,
        hstab, Subgroup.index_bot, Nat.card_zpowers, hgord]
    have hy : y ∈ MulAction.orbit (Subgroup.zpowers g) x := by
      rw [horbit]
      exact Set.mem_univ y
    exact hy
  exact ⟨g, hpre⟩

include W in
/-- On the odd-index-two owner, every induced subrepresentation over a
one-dimensional ternary chief fibre has head at most that fibre dimension.
The proof uses the literal six-cycle supplied by the nonzero relative
head; no character-table or semisimplicity estimate is used. -/
theorem induced_subrepresentationCharacterHead_le_fibre
    [MulAction.IsPretransitive U X]
    (hX : Nat.card X = 6)
    (M₀ : Subgroup U) [M₀.Normal]
    (hM₀ : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M₀) ≠ 0)
    (x : X)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (ρ : Representation (ZMod 3) (MulAction.stabilizer U x) V)
    (S : Subrepresentation
      (Representation.ind (MulAction.stabilizer U x).subtype ρ)) :
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction S.toRepresentation)) ≤
      Module.finrank (ZMod 3) V := by
  obtain ⟨g, hg⟩ := W.exists_six_cycle_of_relativeHead_ne_zero hX M₀ hM₀
  letI : MulAction.IsPretransitive (Subgroup.zpowers g) X := hg
  letI : MulAction.IsPretransitive (Subgroup.zpowers g)
      (U ⧸ MulAction.stabilizer U x) :=
    cyclicQuotientStabilizer_pretransitive g x
  exact induced_subrepresentationCharacterHead_le_fibre_of_pretransitive
    (MulAction.stabilizer U x) ρ g S

end C1OddIndexTwoOwnerWitness

namespace C1CyclicBinaryModuleOwnerWitness

variable {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : C1CyclicBinaryModuleOwnerWitness G)

/-- Evaluate a binary-base-invariant vector in an induced
subrepresentation on the actual ternary complement.  Factorization by the
normal base makes this evaluation injective; equivariance retains the
literal right-translation action of the complement. -/
def invariantEvalComplement
    [W.base.Normal]
    (H : Subgroup G) (ρ : Representation k H V)
    (S : Subrepresentation (Representation.ind H.subtype ρ)) :
    Representation.IntertwiningMap
      ((Representation.toInvariants S.toRepresentation W.base).comp
        W.complement.subtype)
      (Representation.coind (⊥ : Subgroup W.complement).subtype
        (Representation.trivial k (⊥ : Subgroup W.complement) V)) where
  toFun s := ⟨fun p =>
    (inducedElementCoinducedEquiv H ρ s.1.1).1 (p : G), by
      intro h p
      have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.2)
      subst h
      simp⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext p
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 (p : G))
      (map_add (inducedElementCoinducedEquiv H ρ) _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    funext p
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 (p : G))
      (map_smul (inducedElementCoinducedEquiv H ρ) _ _)
  isIntertwining' p := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext q
    change
      (inducedElementCoinducedEquiv H ρ
        (S.toRepresentation (p : G) s.1).1).1 (q : G) =
      (inducedElementCoinducedEquiv H ρ s.1.1).1 ((q : G) * (p : G))
    have he := Representation.IntertwiningMap.isIntertwining _ _
      (inducedElementCoinducedEquiv H ρ).toIntertwiningMap (p : G) s.1.1
    exact congrArg (fun f : Representation.coindV H.subtype ρ => f.1 (q : G)) he

theorem invariantEvalComplement_injective
    [W.base.Normal]
    (H : Subgroup G) (ρ : Representation k H V)
    (S : Subrepresentation (Representation.ind H.subtype ρ)) :
    Function.Injective (invariantEvalComplement W H ρ S) := by
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  apply (inducedElementCoinducedEquiv H ρ).toLinearEquiv.injective
  apply Subtype.ext
  funext x
  let b : W.base := W.factorBase x
  let p : W.complement := W.factorComplement x
  let b' : W.base := normalConjugate W.base W.base_normal b ((p : G)⁻¹)
  have hxbp : (b : G) * (p : G) = x := W.factorization x
  have hpb : (p : G) * (b' : G) = x := by
    calc
      (p : G) * (b' : G) = (b : G) * (p : G) := by
        simp only [b', normalConjugate_coe]
        group
      _ = x := hxbp
  have hsfix :
      inducedElementCoinducedEquiv H ρ s.1.1 =
        Representation.coind H.subtype ρ (b' : G)
          (inducedElementCoinducedEquiv H ρ s.1.1) := by
    have hsB := s.2 b'
    have he := congrArg
      (fun z : S.toSubmodule => inducedElementCoinducedEquiv H ρ z.1) hsB
    have hint := Representation.IntertwiningMap.isIntertwining _ _
      (inducedElementCoinducedEquiv H ρ).toIntertwiningMap (b' : G) s.1.1
    exact he.symm.trans hint
  have htfix :
      inducedElementCoinducedEquiv H ρ t.1.1 =
        Representation.coind H.subtype ρ (b' : G)
          (inducedElementCoinducedEquiv H ρ t.1.1) := by
    have htB := t.2 b'
    have he := congrArg
      (fun z : S.toSubmodule => inducedElementCoinducedEquiv H ρ z.1) htB
    have hint := Representation.IntertwiningMap.isIntertwining _ _
      (inducedElementCoinducedEquiv H ρ).toIntertwiningMap (b' : G) t.1.1
    exact he.symm.trans hint
  rw [← hpb]
  have hsval := congrArg
    (fun f : Representation.coindV H.subtype ρ => f.1 (p : G)) hsfix
  have htval := congrArg
    (fun f : Representation.coindV H.subtype ρ => f.1 (p : G)) htfix
  change
    (inducedElementCoinducedEquiv H ρ s.1.1).1 (p : G) =
      (inducedElementCoinducedEquiv H ρ s.1.1).1 ((p : G) * (b' : G)) at hsval
  change
    (inducedElementCoinducedEquiv H ρ t.1.1).1 (p : G) =
      (inducedElementCoinducedEquiv H ρ t.1.1).1 ((p : G) * (b' : G)) at htval
  change
    (inducedElementCoinducedEquiv H ρ s.1.1).1 ((p : G) * (b' : G)) =
      (inducedElementCoinducedEquiv H ρ t.1.1).1 ((p : G) * (b' : G))
  rw [← hsval, ← htval]
  exact congrFun (congrArg Subtype.val hst) p

/-- If the retained complement is the actual group of order three, binary
base averaging collapses every induced subrepresentation to one regular
ternary complement module.  Consequently its invariant-character head is
bounded by the original fibre dimension. -/
theorem induced_subrepresentationCharacterHead_le_fibre
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (hPcard : Nat.card W.complement = 3)
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (S : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction S.toRepresentation)) ≤
      Module.finrank (ZMod 3) V := by
  letI : W.base.Normal := W.base_normal
  letI : Fintype W.base := Fintype.ofFinite W.base
  obtain ⟨n, hn⟩ := W.basePGroup.exists_card_eq
  have hcard3 : (Fintype.card W.base : ZMod 3) ≠ 0 := by
    rw [Fintype.card_eq_nat_card, hn, Nat.cast_pow]
    exact pow_ne_zero n (by decide)
  letI : Invertible (Fintype.card W.base : ZMod 3) :=
    invertibleOfNonzero hcard3
  letI : FiniteDimensional (ZMod 3)
      (Representation.IndV H.subtype ρ) := induced_finiteDimensional H ρ
  let τB := Representation.toInvariants S.toRepresentation W.base
  let τP := τB.comp W.complement.subtype
  let ρ₀ : Representation (ZMod 3) (⊥ : Subgroup W.complement) V :=
    Representation.trivial (ZMod 3) (⊥ : Subgroup W.complement) V
  have hindex : (⊥ : Subgroup W.complement).index = 3 ^ 1 := by
    rw [Subgroup.index_bot, hPcard]
    norm_num
  calc
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction S.toRepresentation)) =
        Module.finrank (ZMod 3)
          (S.toRepresentation.IntertwiningMap
            (Representation.trivial (ZMod 3) G (ZMod 3))) :=
      (representationCharacterHeadEquiv S.toRepresentation).finrank_eq
    _ ≤ Module.finrank (ZMod 3)
          (τB.IntertwiningMap (Representation.trivial (ZMod 3) G (ZMod 3))) :=
      representationHead_le_normalInvariants S.toRepresentation W.base
    _ = Module.finrank (ZMod 3)
          (primeActionCharacters 3 (representationGroupAction τB)) :=
      (representationCharacterHeadEquiv τB).finrank_eq.symm
    _ ≤ Module.finrank (ZMod 3)
          (primeActionCharacters 3 (representationGroupAction τP)) :=
      representationCharacterHead_le_restriction τB W.complement.subtype
    _ ≤ Module.finrank (ZMod 3) V * ternaryLocalWidth 1 :=
      threeGroup_coinduced_injective_characterHead_le W.complementPGroup
        (⊥ : Subgroup W.complement) ρ₀ 1 hindex τP
        (invariantEvalComplement W H ρ S)
        (invariantEvalComplement_injective W H ρ S)
    _ = Module.finrank (ZMod 3) V := by simp

end C1CyclicBinaryModuleOwnerWitness

end SymmetricSubgroupAsymptotics

end
