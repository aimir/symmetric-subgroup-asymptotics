import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap
import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators
import SymmetricSubgroupAsymptotics.PrimeLayerVanishing
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead
import SymmetricSubgroupAsymptotics.SemisimpleChiefWeightQuotientBound
import SymmetricSubgroupAsymptotics.SmallAbelianQuotientPermutationSix

/-! A high actual ternary relative head in nonaffine degree10/12 forces
the actual socle quotient to be the noncyclic group of order9. Its actual
faithful six-point comparator is produced without a primitive census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

private theorem head_le_one_of_cyclic_perfect_quotient
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] [Group.IsPerfect E] [IsCyclic (G⧸E)]
    (hcover : ∀ N : Subgroup G,N.Normal → N≠⊥ → E≤N)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤1 := by
  by_cases hn : N=⊥
  · subst N
    rw [primeRelativeHead_perfect 3]
    exact Nat.zero_le _
  rw [primeRelativeHead_chain_perfect_kernel 3 E N (hcover N inferInstance hn)]
  let Q := normalChainQuotient E N
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic Q)
  rw [Subgroup.zpowers_eq_closure] at hg
  have hgen := primeCharacterRank_le_generators 3 ({g} : Finset Q)
    (by simpa only [Finset.coe_singleton] using hg)
  have hhead := (Submodule.finrank_le (primeRelativeCharacters 3 Q)).trans hgen
  simpa only [Finset.card_singleton] using hhead

namespace PrimitiveSocleRawStructure

private theorem nine_receipt : ∀ q : Fin 11,2≤q.val.factorization 3 → q.val=9 :=
  by decide +kernel

theorem NonaffineData.high_ten_twelve_quotient_nine_noncyclic
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hdegree : Nat.card X=10 ∨ Nat.card X=12)
    (N : Subgroup G) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card (G⧸finiteGroupSocle G)=9 ∧ ¬IsCyclic (G⧸finiteGroupSocle G) := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by omega)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hpow : 2^Nat.card (G⧸finiteGroupSocle G)≤1728 :=
    (quotientOrder_twoPow_le_cube_of_log (by omega) hlog).trans
      (by simpa using Nat.pow_le_pow_left (by omega : ell≤12) 3)
  have hq10 : Nat.card (G⧸finiteGroupSocle G)≤10 := by
    by_contra h
    have hb : 2048≤1728 := calc
      2048=2^11 := by decide
      _ ≤ 2^Nat.card (G⧸finiteGroupSocle G) :=
        pow_le_pow_right₀ (by decide : 1≤(2 : ℕ)) (by omega)
      _ ≤ 1728 := hpow
    omega
  let c := actualChiefSeries G
  have hh := (primeRelativeHead_le_actualChiefWeight N c).trans
    (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
      (finiteGroupSocle G) D.chart c)
  have htwo : 2≤Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by omega
  have hq := nine_receipt ⟨Nat.card (G⧸finiteGroupSocle G),by omega⟩ (by
    change 2≤(Nat.card (G⧸finiteGroupSocle G)).factorization 3
    omega)
  change Nat.card (G⧸finiteGroupSocle G)=9 at hq
  refine ⟨hq,?_⟩
  intro hcyc
  letI : IsCyclic (G⧸finiteGroupSocle G) := hcyc
  letI : Group.IsPerfect (⊤ : Subgroup (finiteGroupSocle G)) :=
    D.chart.normal_subgroup_perfect ⊤
  letI : Group.IsPerfect (finiteGroupSocle G) := Group.IsPerfect.ofSurjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup (finiteGroupSocle G))≃*finiteGroupSocle G).toMonoidHom)
    (Subgroup.topEquiv : (⊤ : Subgroup (finiteGroupSocle G))≃*finiteGroupSocle G).surjective
  have hone := head_le_one_of_cyclic_perfect_quotient (finiteGroupSocle G)
    (D.oneFactor_socle_le hk) N
  omega

theorem NonaffineData.high_ten_twelve_quotient_faithful_six
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hdegree : Nat.card X=10 ∨ Nat.card X=12)
    (N : Subgroup G) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ d : ℕ,0<d ∧ d≤6 ∧
      ∃ f : (G⧸finiteGroupSocle G)→*Equiv.Perm (Fin d),Function.Injective f := by
  obtain ⟨hq,hnc⟩ := D.high_ten_twelve_quotient_nine_noncyclic hindex hdegree N hhigh
  letI : CommGroup (G⧸finiteGroupSocle G) :=
    IsPGroup.commGroupOfCardEqPrimeSq (p := 3) (by simpa only [show (3 : ℕ)^2=9 by decide] using hq)
  exact smallAbelian_noncyclic_faithful_permutation_six (Or.inr hq) hnc

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
