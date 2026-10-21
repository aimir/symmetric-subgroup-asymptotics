import SymmetricSubgroupAsymptotics.PrimitiveTenTwelveHighHeadQuotient

/-! The actual simple-index quotient bound gives relative ternary head at
most2 in the two remaining degrees, without a primitive correspondence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

private theorem capacity_receipt : ∀ q : Fin 11,q.val.factorization 3≤2 := by decide +kernel

theorem NonaffineData.ten_twelve_relativeHead_le_two
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hdegree : Nat.card X=10 ∨ Nat.card X=12)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤2 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by omega)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hpow : 2^Nat.card (G⧸finiteGroupSocle G)≤1728 :=
    (quotientOrder_twoPow_le_cube_of_log (by omega) hlog).trans
      (by simpa using Nat.pow_le_pow_left (by omega : ell≤12) 3)
  have hq : Nat.card (G⧸finiteGroupSocle G)<11 := by
    by_contra h
    have hb : 2048≤1728 := calc
      2048=2^11 := by decide
      _ ≤ 2^Nat.card (G⧸finiteGroupSocle G) :=
        pow_le_pow_right₀ (by decide : 1≤(2 : ℕ)) (by omega)
      _ ≤ 1728 := hpow
    omega
  let c := actualChiefSeries G
  exact ((primeRelativeHead_le_actualChiefWeight N c).trans
    (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
      (finiteGroupSocle G) D.chart c)).trans (capacity_receipt ⟨_,hq⟩)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
