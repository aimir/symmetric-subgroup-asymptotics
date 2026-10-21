import SymmetricSubgroupAsymptotics.PrimitiveSocleTwoActionHeadReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! The primitive degree18 consumer needs head at most two, rather than
an exact vanishing statement. Its actual outer quotient has order below15
by the ordinary retained simple-index bound, which suffices directly. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

private theorem eighteen_not_two_power (d : ℕ) : 18≠2^d := by
  intro h
  by_cases hd : d<5
  · interval_cases d <;> norm_num at h
  · have h5 : 5≤d := by omega
    have h32 : (32 : ℕ)≤2^d := pow_le_pow_right₀ (by decide : (1 : ℕ)≤2) h5
    omega

theorem primitive_degreeEighteen_ternaryHead_le_two_without_catalogue
    (hindex : PublishedSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=18) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤2 := by
  cases Classical.choice (publishedONanScottStructure G X) with
  | inl D =>
      obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
      have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
        (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) hell.1
      have horder := (hindex D.Simple D.noncommutative ell hell).1
      have hd := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
      rw [hX] at hd
      have hk : D.factorCount=1 := by
        by_contra h
        have hk2 : 2≤D.factorCount := by have hp:=D.factorCount_pos;omega
        have h25 : 25≤ell^D.factorCount := calc
          25=5^2 := by decide
          _ ≤ ell^2 := Nat.pow_le_pow_left hf 2
          _ ≤ ell^D.factorCount := pow_le_pow_right₀ (by omega : 1≤ell) hk2
        omega
      letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
      letI : Group.IsPerfect (finiteGroupSocle G) :=
        Group.IsPerfect.ofSurjective (f := (D.oneFactorEquiv hk).symm.toMonoidHom)
          (D.oneFactorEquiv hk).symm.surjective
      have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique
        3 (finiteGroupSocle G) (D.oneFactor_socle_le hk) N
      have hb := ternaryValuation_le_two_of_lt_fifteen _
        (D.oneFactor_quotient_order_lt_fifteen hk hindex (by omega))
      omega
  | inr P =>
      let x : X := Classical.choice inferInstance
      letI : Fact P.p.Prime := ⟨P.p_prime⟩
      obtain ⟨d,hd⟩ := P.V_pgroup.exists_card_eq
      have he : 18=P.p^d := hX.symm.trans ((P.card_eq x).symm.trans hd)
      have hp : P.p=2 := by
        rcases P.p_prime.eq_two_or_odd' with hp|hp
        · exact hp
        · have ho : Odd 18 := he.symm ▸ hp.pow
          exact ((by decide : ¬Odd 18) ho).elim
      rw [hp] at he
      exact (eighteen_not_two_power d he).elim

end SymmetricSubgroupAsymptotics
