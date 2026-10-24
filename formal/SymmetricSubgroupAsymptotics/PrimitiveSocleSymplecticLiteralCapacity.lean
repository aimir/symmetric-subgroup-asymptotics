import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound

/-! Component capacity on the literal elementary symplectic quotient.
Simplicity belongs to that same quotient. In particular, the theorem can
be used after transporting an original characteristic-two B model to its
natural symplectic realization; no independent C-model simplicity is needed.
The actual proper-index estimate and scalar budget are explicit inputs to
this reusable adapter, rather than asserted classification facts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticLiteralCapacity
open CFSGSymplecticSerreMatrices CFSGSymplecticSharpOrderUpper
open CFSGReduction PrimitiveSocleRawStructure

theorem component_le_field_power (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (elementaryProjective q.Field r)] :
    Nat.card (elementaryProjective q.Field r) *
      Nat.card (Outer (elementaryProjective q.Field r)) ≤ q.order^(2*r^2+r+3) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s+2 := ⟨r-2, by omega⟩
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hc : 3 ≤ q.order^2 := (by decide : 3 ≤ (2 : ℕ)^2).trans
    (Nat.pow_le_pow_left hq 2)
  have ho : Nat.card (Outer (elementaryProjective q.Field (s+2))) ≤ 3*q.exponent := by
    simpa only [Nat.add_assoc, Nat.reduceAdd,
      CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      CFSGSymplecticPointRootLabels.outer_card_le_three_ringAut
        (K := q.Field) q.prime (s+1) (by omega)
  have houter : Nat.card (Outer (elementaryProjective q.Field (s+2))) ≤ q.order^3 :=
    (ho.trans (Nat.mul_le_mul hc hf)).trans_eq (pow_succ q.order 2).symm
  have hquot : Nat.card (elementaryProjective q.Field (s+2)) ≤
      Nat.card (elementaryRootGroup q.Field (s+2)) :=
    Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup q.Field (s+2))))
      (QuotientGroup.mk'_surjective _)
  have horder : Nat.card (elementaryProjective q.Field (s+2)) ≤
      q.order^(2*(s+2)^2+(s+2)) := hquot.trans (by
    simpa only [q.card_field] using elementary_card_le_quadratic_power q.Field (s+2))
  exact (Nat.mul_le_mul horder houter).trans_eq (pow_add _ _ _).symm

theorem order_ge_1024_of_proper_index (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (elementaryProjective q.Field r)] (b : ℕ) (hb : 32 ≤ b)
    (hindex : ∀ K : Subgroup (elementaryProjective q.Field r), K ≠ ⊤ → b ≤ K.index) :
    1024 ≤ Nat.card (elementaryProjective q.Field r) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s+1 := ⟨r-1, by omega⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (elementaryProjective q.Field (s+1))
  obtain ⟨K, hK, he⟩ := hell.1
  have hlo : 32 ≤ ell := hb.trans ((hindex K hK).trans_eq he)
  have hs := elementary_leastProperIndex_square_lt_card q.Field s (by omega)
    (by omega : s+1 = 2 → Nat.card q.Field ≠ 2) ell hell
  exact ((by decide : 1024 ≤ (32 : ℕ)^2).trans
    (Nat.pow_le_pow_left hlo 2)).trans hs.le

end SymmetricSubgroupAsymptotics.CFSGSymplecticLiteralCapacity

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGSymplecticSerreMatrices CFSGReduction CFSGSymplecticLiteralCapacity
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_symplectic_literal_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* elementaryProjective q.Field r) (b : ℕ) (hb : 32 ≤ b)
    (hindex : ∀ K : Subgroup (elementaryProjective q.Field r), K ≠ ⊤ → b ≤ K.index)
    (hcube : q.order^(3*(2*r^2+r+3)) ≤ 5^(b-1)) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (elementaryProjective q.Field r) := e.symm.isSimpleGroup
  refine D.subgroup_class_cube_le_of_component_order_cube b (by omega) ?_ ?_ ?_ H
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    exact (hindex (K.map e.toMonoidHom) hmap).trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    have hp := Nat.pow_le_pow_left (component_le_field_power r (by omega) q) 3
    rw [← pow_mul, Nat.mul_comm (2*r^2+r+3) 3] at hp
    exact hp.trans hcube
  · rw [Nat.card_congr e.toEquiv]
    exact order_ge_1024_of_proper_index r hr q b hb hindex

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
