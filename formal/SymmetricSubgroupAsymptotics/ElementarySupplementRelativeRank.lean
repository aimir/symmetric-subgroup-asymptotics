import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralAbelianSupplement
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelGenerators
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality

/-! An elementary supplement makes every invariant character extendible.
The proof identifies the SAME original relative radical with the absolute
prime-evaluation kernel, then uses literal subgroup indices. In particular
proper full-top normals save the actual quotient exponent in their normal
rank; no split-extension premise is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (E N : Subgroup G) [N.Normal]
    (hsup : E ⊔ N = ⊤) (hE : IsMulCommutative E)
    (hexp : ∀ e : E, e ^ p = 1)

include hsup hE hexp

/-- The relative radical is exactly the original absolute prime kernel
when the displayed normal subgroup has an elementary abelian supplement. -/
theorem primeRelativeRadical_eq_evaluationKernel_of_elementary_supplement :
    primeRelativeRadical p N = (primeAbelianizationGroupMap p G).ker := by
  let R := primeRelativeRadical p N
  let q : G →* G ⧸ R := QuotientGroup.mk' R
  have hcomm : IsMulCommutative (G ⧸ R) :=
    TwelvePointRemainingStructural.relativeRadicalQuotient_commutative p E N hsup hE
  letI : CommGroup (G ⧸ R) := {
    (inferInstance : Group (G ⧸ R)) with mul_comm := hcomm.is_comm.comm }
  have hpowers (g : G) : g ^ p ∈ R := by
    obtain ⟨e, he, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
      (show g ∈ E ⊔ N by rw [hsup]; trivial)
    apply (QuotientGroup.eq_one_iff (N := R) _).mp
    change q ((e * n) ^ p) = 1
    have heq : q e ^ p = 1 := by
      rw [← map_pow]
      have hepow : e ^ p = 1 := congrArg Subtype.val (hexp ⟨e, he⟩)
      rw [hepow, map_one]
    have hnq : q n ^ p = 1 :=
      primeRelativeRadical_image_pow_eq_one p N ⟨q n, ⟨n, hn, rfl⟩⟩
    rw [map_pow, map_mul, mul_pow, heq, hnq, mul_one]
  have hderived : commutator G ≤ R :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  apply le_antisymm (primeRelativeRadical_le_ambient_evaluation_ker p N)
  rw [primeAbelianizationGroupMap_ker_eq_generated_powers_sup_commutator
    p (fun g : G => g) (by simp)]
  apply sup_le _ hderived
  apply (Subgroup.closure_le R).mpr
  rintro _ ⟨g, rfl⟩
  exact hpowers g

/-- Exact relative and absolute ranks retain the literal index of the
same original normal subgroup. Finiteness is the only group hypothesis. -/
theorem primeRelativeHead_add_indexExponent_eq_of_elementary_supplement
    [Finite G] (j : ℕ) (hindex : N.index = p ^ j) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) + j =
      Module.finrank (ZMod p) (PrimeCharacters p G) := by
  let R := primeRelativeRadical p N
  have hker : R = (primeAbelianizationGroupMap p G).ker :=
    primeRelativeRadical_eq_evaluationKernel_of_elementary_supplement p E N hsup hE hexp
  have hrelative : R.relIndex N = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
    have he : R.subgroupOf N = primeRelativeRadicalKernel p N := by
      ext n
      exact coe_mem_primeRelativeRadical_iff p N n
    change Nat.card (N ⧸ R.subgroupOf N) = _
    rw [he]
    exact primeRelativeRadical_quotient_card p N
  have habsolute : R.index = p ^ Module.finrank (ZMod p) (PrimeCharacters p G) := by
    rw [hker, Subgroup.index_ker,
      (primeAbelianizationGroupMap p G).range_eq_top_of_surjective
        (primeAbelianizationGroupMap_surjective p G),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card (PrimeAbelianization p G) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Subspace.dual_finrank_eq,
      Nat.card_zmod]
  have hm := Subgroup.relIndex_mul_index (primeRelativeRadical_le p N)
  change R.relIndex N * N.index = R.index at hm
  rw [hrelative, hindex, habsolute, ← pow_add] at hm
  exact Nat.pow_right_injective (Fact.out : p.Prime).one_lt hm

/-- Relative Burnside basis converts the same exact identity into literal
ambient normal-generator numbers for a finite p-group. -/
theorem normalGen_add_indexExponent_eq_of_elementary_supplement
    [Finite G] (hG : IsPGroup p G) (j : ℕ) (hindex : N.index = p ^ j) :
    MarkedC4.normalGen N + j = Module.finrank (ZMod p) (PrimeCharacters p G) := by
  rw [pGroup_normalGen_eq_primeRelativeHead p hG N]
  exact primeRelativeHead_add_indexExponent_eq_of_elementary_supplement
    p E N hsup hE hexp j hindex

end SymmetricSubgroupAsymptotics
