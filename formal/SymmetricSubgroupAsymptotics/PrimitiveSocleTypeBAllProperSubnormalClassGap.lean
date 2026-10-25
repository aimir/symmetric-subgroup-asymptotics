import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBPointRadicalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticAllProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv

/-! Every original type-B model pays the proper-subnormal extra gap.
Odd fields use the same point-radical order packet. Characteristic two
uses the proved original-B-to-literal-symplectic equivalence and the
checked literal packets, without assuming original-C simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGOrthogonalBilinearComponentOrderCube
open OrthogonalPointRadicalOrderCubeNumerics CFSGSymplecticSerreMatrices
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeB_point_radical
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hodd : q.prime≠2) (e : D.Simple ≃* CFSG.Models.B r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.B r q) := Finite.of_equiv D.Simple e.toEquiv
  have hp : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
  have hq : 3 ≤ q.order := hp.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex : ∀ K : Subgroup (CFSG.Models.B r q), K ≠ ⊤ →
      oddIndex q.order r ≤ K.index := by
    intro K hK
    exact typeB_point_radical_le_proper_index r hr q hodd K hK
  have hb : 32 ≤ oddIndex q.order r := by
    have ht : 9 ≤ q.order^(r-1) := (by decide : 9 ≤ (3 : ℕ)^2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) (by omega)))
    unfold oddIndex
    have hs : 8 ≤ q.order^(r-1)-1 := by omega
    exact (by decide : 32 ≤ 8*9).trans (Nat.mul_le_mul hs ht)
  have hcube : q.order^(3*componentExponent r) ≤ 5^(oddIndex q.order r-1) :=
    odd_order_cube q.order r hq hr
  have hbase : (Nat.card (CFSG.Models.B r q)*Nat.card (Outer (CFSG.Models.B r q)))^3 ≤
      5^(oddIndex q.order r-1) := by
    have ho := typeB_component_le_field_power r hr q
    have he : 2*r^2+3*r+4 ≤ componentExponent r := by unfold componentExponent; omega
    have hpow := Nat.pow_le_pow_left
      (ho.trans (Nat.pow_le_pow_right (by omega : 0<q.order) he)) 3
    rw [← pow_mul, Nat.mul_comm (componentExponent r) 3] at hpow
    exact hpow.trans hcube
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.B r q) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (CFSG.Models.B r q)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 32 ≤ ell := hb.trans ((hindex K hK).trans_eq he)
    have hs := (typeB_simpleIndexBounds r hr q ell hell).1
    exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans (Nat.pow_le_pow_left hlo 2)).trans hs.le
  exact D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.B r q) e (oddIndex q.order r) (by omega) hindex hbase hlarge H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeB_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.B r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hp : q.prime=2
  · letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
    letI : CharP q.Field 2 := by rw [← hp]; infer_instance
    have hE : Nonempty (D.Simple ≃* elementaryProjective q.Field r) := by
      obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
      exact ⟨e.trans (CFSGOrthogonalBSerreMatrices.serreProjectiveEquivSymplecticProjective_charTwo
        q.Field (s+2) (by omega))⟩
    let E := Classical.choice hE
    by_cases hwindow : 4 ≤ q.order ∨ 5 ≤ r
    · exact D.proper_subnormal_class_cube_le_of_symplectic_binary_higher_literal
        r hr q hp E hwindow H hH hne
    have he : q.exponent=1 := by
      by_contra hh
      have htwo : 2 ≤ q.exponent := by have := q.exponent_pos; omega
      apply hwindow
      left
      change 4 ≤ q.prime^q.exponent
      rw [hp]
      exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) htwo
    have hq2 : q.order=2 := by change q.prime^q.exponent=2; rw [hp,he,pow_one]
    have hrank : r=3 ∨ r=4 := by omega
    rcases hrank with rfl | rfl
    · exact D.proper_subnormal_class_cube_le_of_binary_rank_three_literal q hq2 E H hH hne
    · exact D.proper_subnormal_class_cube_le_of_symplectic_binary_point_rank_four_literal
        q hq2 E H hH hne
  · exact D.proper_subnormal_class_cube_le_of_typeB_point_radical r hr q hp e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
