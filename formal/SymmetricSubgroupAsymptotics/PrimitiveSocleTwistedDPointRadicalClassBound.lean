import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
import SymmetricSubgroupAsymptotics.OrthogonalPointRadicalOrderCubeNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound

/-! The actual minus-orthogonal point radical pays every original
component capacity in fields of order at least three and binary ranks
at least five. Every socle factor and both degree forms are retained.
Binary rank four is excluded explicitly; no prime multiplier is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGOrthogonalBilinearComponentOrderCube
open OrthogonalPointRadicalOrderCubeNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_twistedD_point_radical
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hwindow : 3 ≤ q.order ∨ 5 ≤ r)
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex : ∀ K : Subgroup (CFSG.Models.TwistedD r q), K ≠ ⊤ →
      minusIndex q.order r ≤ K.index := by
    intro K hK
    exact typeTwistedD_point_radical_le_proper_index r hr q K hK
  have hb : 32 ≤ minusIndex q.order r := minusIndex_ge_thirtyTwo q.order r hq hr hwindow
  have hcube : q.order^(3*componentExponent r) ≤ 5^(minusIndex q.order r-1) := by
    by_cases hq3 : 3 ≤ q.order
    · exact minus_odd_order_cube q.order r hq3 hr
    · have hq2 : q.order = 2 := by omega
      have hr5 : 5 ≤ r := hwindow.resolve_left hq3
      simpa only [hq2] using minus_binary_order_cube r hr5
  have hbase : (Nat.card (CFSG.Models.TwistedD r q)*Nat.card (Outer (CFSG.Models.TwistedD r q)))^3 ≤
      5^(minusIndex q.order r-1) := by
    have ho := typeTwistedD_component_le_field_power r hr q hnc
    have he : 2*r^2+r+4 ≤ componentExponent r := by unfold componentExponent; omega
    have hp := Nat.pow_le_pow_left
      (ho.trans (Nat.pow_le_pow_right (by omega : 0 < q.order) he)) 3
    rw [← pow_mul, Nat.mul_comm (componentExponent r) 3] at hp
    exact hp.trans hcube
  have hlarge : 1024 ≤ Nat.card (CFSG.Models.TwistedD r q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.TwistedD r q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hlo : 32 ≤ ell := hb.trans ((hindex K hK).trans_eq he)
    have hs := typeTwistedD_leastProperIndex_square_lt_card r q hr ell hell
    exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans
      (Nat.pow_le_pow_left hlo 2)).trans hs.le
  refine D.subgroup_class_cube_le_of_component_order_cube (minusIndex q.order r)
    (by omega) ?_ ?_ ?_ H
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    exact (hindex (K.map e.toMonoidHom) hmap).trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact hbase
  · rw [Nat.card_congr e.toEquiv]
    exact hlarge

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
