import SymmetricSubgroupAsymptotics.PrimeLayerVanishing
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import SymmetricSubgroupAsymptotics.PrimeRelativeRadical
import SymmetricSubgroupAsymptotics.BinaryCoverage
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Relative prime heads above a primitive perfect socle

This file isolates the group-theoretic part of the bounded primitive
ternary calculation.  Let `E ◁ L` be a perfect minimal normal subgroup and
assume that its centralizer in `L` is contained in `E`.  Every normal
subgroup `N ◁ L` either misses `E`, in which case it is trivial, or contains
`E`, in which case its relative prime head is carried entirely by the
literal quotient `N/E`.  Consequently the head is bounded by the
`p`-valuation of `|L/E|`.

The theorem is independent of a primitive-group catalogue.  A published
O'Nan--Scott or finite catalogue row only has to provide the actual socle,
minimality, perfection, self-centralization and the quotient order.
-/

set_option autoImplicit false
noncomputable section

open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- The elementary prime quotient detected by all prime characters has
cardinality dividing the order of the original finite group. -/
theorem primeCharacters_pow_finrank_dvd_card
    (G : Type*) [Group G] [Finite G] :
    p ^ Module.finrank (ZMod p) (PrimeCharacters p G) ∣ Nat.card G := by
  let π := primeAbelianizationGroupMap p G
  have hquot : Nat.card (G ⧸ π.ker) =
      p ^ Module.finrank (ZMod p) (PrimeCharacters p G) := by
    rw [Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective π
        (primeAbelianizationGroupMap_surjective p G)).toEquiv]
    change Nat.card (PrimeAbelianization p G) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := PrimeAbelianization p G), Nat.card_zmod,
      Subspace.dual_finrank_eq]
  rw [← hquot]
  exact π.ker.card_quotient_dvd_card

/-- A minimal self-centralizing normal subgroup with zero relative
`p`-head removes every character below it.  What remains is paid by the
exact prime valuation of the ambient quotient order.  This is the form
used both for a perfect nonabelian socle and for an irreducible affine
socle. -/
theorem primeRelativeHead_le_quotientFactorization_of_minimalHeadZero
    {L : Type*} [Group L] [Finite L]
    (E : Subgroup L) [E.Normal]
    (hminimal : ∀ B : Subgroup L, B.Normal → B ≤ E → B = ⊥ ∨ B = E)
    (hself : ∀ x : L, (∀ e : E, x * (e : L) = (e : L) * x) → x ∈ E)
    (hzero : Module.finrank (ZMod p) (primeRelativeCharacters p E) = 0)
    (N : Subgroup L) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      (Nat.card (L ⧸ E)).factorization p := by
  let B : Subgroup L := N ⊓ E
  have hBnormal : B.Normal := inferInstance
  rcases hminimal B hBnormal inf_le_right with hB | hB
  · have hNbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxE : x ∈ E := hself x (fun e => by
        have hc : ⁅x, (e : L)⁆ ∈ B := by
          exact ⟨Subgroup.commutator_le_left N E
              (Subgroup.commutator_mem_commutator hx e.2),
            Subgroup.commutator_le_right N E
              (Subgroup.commutator_mem_commutator hx e.2)⟩
        have hc1 : ⁅x, (e : L)⁆ = 1 := by
          have : ⁅x, (e : L)⁆ ∈ (⊥ : Subgroup L) := hB ▸ hc
          exact this
        change x * (e : L) * x⁻¹ * (e : L)⁻¹ = 1 at hc1
        calc
          x * (e : L) =
              (x * (e : L) * x⁻¹ * (e : L)⁻¹) * ((e : L) * x) := by
                group
          _ = (e : L) * x := by rw [hc1, one_mul])
      have hxB : x ∈ B := ⟨hx, hxE⟩
      have : x ∈ (⊥ : Subgroup L) := hB ▸ hxB
      exact this
    have hNsub : Subsingleton N := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : (x : L) = 1 := by
        have : (x : L) ∈ (⊥ : Subgroup L) := hNbot ▸ x.2
        exact this
      have hy : (y : L) = 1 := by
        have : (y : L) ∈ (⊥ : Subgroup L) := hNbot ▸ y.2
        exact this
      exact hx.trans hy.symm
    letI : Subsingleton N := hNsub
    letI : Subsingleton (PrimeCharacters p N) :=
      ⟨fun χ ψ => AddMonoidHom.ext fun n => by
        have hn : n = 0 := Subsingleton.elim _ _
        rw [hn, map_zero, map_zero]⟩
    exact (Module.finrank_zero_of_subsingleton (R := ZMod p)
      (M := primeRelativeCharacters p N)).le.trans (Nat.zero_le _)
  · have hEN : E ≤ N := by
      intro e he
      have : e ∈ B := hB.symm ▸ he
      exact this.1
    have hhead := primeRelativeHead_chain_le E N p hEN
    rw [hzero, zero_add] at hhead
    apply hhead.trans
    let d := Module.finrank (ZMod p)
      (primeRelativeCharacters p (normalChainQuotient E N))
    have hdvd : p ^ d ∣ Nat.card (L ⧸ E) :=
      (pow_dvd_pow p (Submodule.finrank_le
        (primeRelativeCharacters p (normalChainQuotient E N)))).trans
        ((primeCharacters_pow_finrank_dvd_card p
          (normalChainQuotient E N)).trans
            (Subgroup.card_subgroup_dvd_card (normalChainQuotient E N)))
    have hfac := (Nat.factorization_le_iff_dvd
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (Nat.card_pos.ne')).mpr hdvd
    have hp := hfac p
    simpa only [Nat.factorization_pow_self (Fact.out : p.Prime)] using hp

/-- In a finite primitive action, a minimal self-centralizing normal subgroup
has zero relative `p`-head unless the action has degree exactly `p`.

Indeed its relative evaluation radical is ambient-normal, hence is either
trivial or the whole minimal normal subgroup.  In the latter case every
relative character vanishes.  In the former case relative evaluation
separates the subgroup, so invariance makes it central in the ambient group;
self-centralization then makes it the whole group.  Its order is a power of
`p`, and a maximal point stabilizer in a finite `p`-group has index `p`.
This forces the primitive degree to be `p`. -/
theorem primeRelativeHead_minimalSelfCentralizing_eq_zero_of_primitive
    {L X : Type*} [Group L] [Finite L] [Finite X] [MulAction L X]
    [MulAction.IsPreprimitive L X] [Nontrivial X]
    (E : Subgroup L) [E.Normal]
    (hminimal : ∀ B : Subgroup L, B.Normal → B ≤ E → B = ⊥ ∨ B = E)
    (hself : ∀ x : L, (∀ e : E, x * (e : L) = (e : L) * x) → x ∈ E)
    (hdegree : Nat.card X ≠ p) :
    Module.finrank (ZMod p) (primeRelativeCharacters p E) = 0 := by
  let R := primeRelativeRadical p E
  have hRE : R ≤ E := primeRelativeRadical_le p E
  rcases hminimal R inferInstance hRE with hR | hR
  · have hker : primeRelativeRadicalKernel p E = ⊥ := by
      apply Subgroup.map_injective E.subtype_injective
      change primeRelativeRadical p E = ⊥ at hR
      simpa only [Subgroup.map_bot] using hR
    have heval : Function.Injective (primeRelativeEvaluation p E) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have hEL : E = ⊤ := by
      apply top_unique
      intro x _
      apply hself x
      intro e
      have hconj :
          (⟨x * (e : L) * x⁻¹,
            Subgroup.Normal.conj_mem inferInstance _ e.2 x⟩ : E) = e := by
        apply heval
        exact primeRelativeEvaluation_conjugate p E x e
      have hcoe := congrArg (fun z : E => (z : L)) hconj
      change x * (e : L) * x⁻¹ = (e : L) at hcoe
      calc
        x * (e : L) = (x * (e : L) * x⁻¹) * x := by group
        _ = (e : L) * x := by rw [hcoe]
    have hcard : Nat.card L =
        p ^ Module.finrank (ZMod p) (primeRelativeCharacters p E) := by
      have hf := primeRelativeRadical_card_factorization p E
      change primeRelativeRadical p E = ⊥ at hR
      rw [hR, Subgroup.card_bot] at hf
      calc
        Nat.card L = Nat.card E := by rw [hEL, Subgroup.card_top]
        _ = _ := by simpa only [mul_one] using hf
    letI hLp : IsPGroup p L := IsPGroup.iff_card.mpr
      ⟨Module.finrank (ZMod p) (primeRelativeCharacters p E), hcard⟩
    let x : X := Classical.choice (inferInstance : Nonempty X)
    have hindex := pGroup_coatom_index hLp (MulAction.stabilizer L x)
      (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := L) x)
    have htrans : MulAction.IsPretransitive L X := inferInstance
    have hdegreeEq : Nat.card X = p := by
      rw [← MulAction.index_stabilizer_of_transitive L x]
      exact hindex
    exact (hdegree hdegreeEq).elim
  · letI : Subsingleton (primeRelativeCharacters p E) := ⟨by
      intro χ ψ
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro eAdd
      let e : E := eAdd.toMul
      have heR : (e : L) ∈ R := hR.symm ▸ e.2
      have hχ : χ.1 (Additive.ofMul e) = 0 :=
        (mem_primeRelativeRadical_iff p E (e : L)).mp heR |>.2 χ
      have hψ : ψ.1 (Additive.ofMul e) = 0 :=
        (mem_primeRelativeRadical_iff p E (e : L)).mp heR |>.2 ψ
      exact hχ.trans hψ.symm⟩
    exact Module.finrank_zero_of_subsingleton

/-- A perfect minimal self-centralizing normal subgroup is the principal
nonaffine specialization of the preceding theorem. -/
theorem primeRelativeHead_le_quotientFactorization_of_minimalPerfect
    {L : Type*} [Group L] [Finite L]
    (E : Subgroup L) [E.Normal] [Group.IsPerfect E]
    (hminimal : ∀ B : Subgroup L, B.Normal → B ≤ E → B = ⊥ ∨ B = E)
    (hself : ∀ x : L, (∀ e : E, x * (e : L) = (e : L) * x) → x ∈ E)
    (N : Subgroup L) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      (Nat.card (L ⧸ E)).factorization p := by
  apply primeRelativeHead_le_quotientFactorization_of_minimalHeadZero
    p E hminimal hself
  exact primeRelativeHead_perfect p E

end SymmetricSubgroupAsymptotics

end
