import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Abelianization.Finite

/-! A cyclic quotient over an actual normal subgroup gives a lower bound
for the FULL abelianization order. No elementary-exponent assertion is made
about that abelianization, and no monotonicity of normalGen is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]

/-- The relative radical contains the whole derived subgroup whenever the
original quotient by the normal subgroup is cyclic. -/
theorem commutator_le_primeRelativeRadical_of_cyclic_quotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    commutator G ≤ primeRelativeRadical p N := by
  let R := primeRelativeRadical p N
  have hRN : R ≤ N := primeRelativeRadical_le p N
  let f : G ⧸ R →* G ⧸ N :=
    QuotientGroup.map R N (MonoidHom.id G) hRN
  have hcenter : f.ker ≤ Subgroup.center (G ⧸ R) := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
    have hg : g ∈ N := by
      apply (QuotientGroup.eq_one_iff g).mp
      exact hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R y
    symm
    rw [← map_mul, ← map_mul]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hc : ⁅g,y⁆ ∈ R := commutator_mem_primeRelativeRadical p N ⟨g,hg⟩ y
    convert hc using 1 <;> simp only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  haveI : IsMulCommutative (G ⧸ R) :=
    ⟨⟨commutative_of_cyclic_center_quotient f hcenter⟩⟩
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- The original cyclic quotient and the whole-ambient relative head are
paid together by the full abelianization. -/
theorem primeRelativeHead_mul_index_le_abelianization_card
    [Finite G] (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) * N.index ≤
      Nat.card (Abelianization G) := by
  let R := primeRelativeRadical p N
  have hR : commutator G ≤ R :=
    commutator_le_primeRelativeRadical_of_cyclic_quotient p N
  have hc : Nat.card (G ⧸ R) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) * N.index := by
    have hN := primeRelativeRadical_card_factorization p N
    have hwhole := N.card_mul_index
    have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    have hpos : 0 < Nat.card R := Nat.card_pos
    change Nat.card N = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) *
      Nat.card R at hN
    have heq : Nat.card (G ⧸ R) * Nat.card R =
        (p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) * N.index) * Nat.card R := by
      calc
        _ = Nat.card G := hquot.symm
        _ = Nat.card N * N.index := hwhole.symm
        _ = _ := by rw [hN]; ring
    nlinarith
  let f : Abelianization G →* G ⧸ R :=
    QuotientGroup.map (commutator G) R (MonoidHom.id G) hR
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective R x
    exact ⟨Abelianization.of g,rfl⟩
  rw [← hc]
  exact Nat.card_le_card_of_surjective f hf

/-- A literal index-p normal subgroup, without an enlargement step. -/
theorem pGroup_normalGen_prime_index_le_abelianization_card
    [Finite G] (hG : IsPGroup p G) (N : Subgroup G) [N.Normal]
    (hindex : N.index = p) :
    p ^ MarkedC4.normalGen N * p ≤ Nat.card (Abelianization G) := by
  have hcard : Nat.card (G ⧸ N) = p := N.index_eq_card.symm.trans hindex
  letI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  simpa only [← pGroup_normalGen_eq_primeRelativeHead p hG N, hindex] using
    primeRelativeHead_mul_index_le_abelianization_card p N

end SymmetricSubgroupAsymptotics
