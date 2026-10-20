import SymmetricSubgroupAsymptotics.PrimitiveAffinePublishedSmallStructuralInput
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! A soluble primitive permutation group satisfies the strong cubic form
of Dixon's order bound. The bounded range uses the retained primitive
catalogue; the infinite range uses the retained soluble irreducible linear
cube bound on the actual affine complement. No order bound on an arbitrary
soluble permutation group is assumed here. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SolublePermutationOrderProof
open Non2UnipotentPrefixFiniteMenu

private theorem row_order_bound : ∀ i : Fin 336,
    (primitiveCompositionBoundRow i).kind = .orderBound →
    (primitiveCompositionBoundRow i).groupOrder ^ 3 ≤
      24 ^ ((primitiveCompositionBoundRow i).degree - 1) := by
  decide +kernel

theorem polynomial_le_exponential (n : ℕ) (hn : 10 ≤ n) :
    n ^ 12 ≤ 24 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have hratio : 10 * (n + 1) ≤ 11 * n := by omega
    have hp := Nat.pow_le_pow_left hratio 12
    have hnum : 11 ^ 12 ≤ 24 * 10 ^ 12 := by decide +kernel
    have hstep : (n + 1) ^ 12 ≤ 24 * n ^ 12 := by
      refine Nat.le_of_mul_le_mul_left (c := 10 ^ 12) ?_ (by decide)
      calc
        10 ^ 12 * (n + 1) ^ 12 ≤ 11 ^ 12 * n ^ 12 := by
          simpa only [mul_pow] using hp
        _ ≤ (24 * 10 ^ 12) * n ^ 12 := Nat.mul_le_mul_right _ hnum
        _ = 10 ^ 12 * (24 * n ^ 12) := by ring
    calc
      (n + 1) ^ 12 ≤ 24 * n ^ 12 := hstep
      _ ≤ 24 * 24 ^ (n - 1) := Nat.mul_le_mul_left _ ih
      _ = 24 ^ (n + 1 - 1) := by
        rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
        omega

private theorem alternating_not_solvable (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSolvable (alternatingGroup (Fin n)) := by
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  intro h
  have hc : IsMulCommutative (alternatingGroup (Fin n)) :=
    ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr h⟩⟩
  rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hc
  simp only [Nat.card_fin] at hc
  omega

theorem bounded_primitive_order
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    [IsSolvable G] (hn : Nat.card X < 45) :
    Nat.card G ^ 3 ≤ 24 ^ (Nat.card X - 1) := by
  obtain ⟨M⟩ := catalogue G X hn
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
    simpa only [M.order_eq hk, M.degree_eq] using row_order_bound M.row hk
  | naturalAlternating =>
    let e := Classical.choice (M.alternating_equiv hk)
    haveI : IsSolvable (alternatingGroup (Fin (Nat.card X))) :=
      solvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (alternating_not_solvable _ (by
      simpa only [M.degree_eq] using
        (primitiveCompositionBoundRow M.row).natural_degree (by rw [hk]; decide)) inferInstance).elim
  | naturalSymmetric =>
    let e := Classical.choice (M.symmetric_equiv hk)
    haveI : IsSolvable (Equiv.Perm (Fin (Nat.card X))) :=
      solvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (alternating_not_solvable _ (by
      simpa only [M.degree_eq] using
        (primitiveCompositionBoundRow M.row).natural_degree (by rw [hk]; decide)) inferInstance).elim

theorem affine_order_le_fourth
    (hbase : HalasiMarotiSolubleIrreducibleCubeBound)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    [IsSolvable G] (P : PrimitiveAffineProfile G X) :
    Nat.card G ≤ Nat.card X ^ 4 := by
  let C := P.elementaryChart (inferInstance : MulAction.IsPreprimitive G X)
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    (C.equiv.symm.injective.comp Multiplicative.ofAdd.injective)
  let x : X := Classical.arbitrary X
  have hV : Nat.card C.V = Nat.card X := by
    change Nat.card (Multiplicative C.V) = Nat.card X
    exact (Nat.card_congr C.equiv.toEquiv).symm.trans (P.card_eq x)
  have hR := hbase (G := P.complement x) (V := C.V) inferInstance
    (P.complementRepresentation inferInstance C x).ρ
    (P.complementRepresentation_irreducible inferInstance C x)
    (P.complementRepresentation_injective inferInstance C x)
  have hcard := (P.isComplement'_complement x).card_mul
  calc
    Nat.card G = Nat.card P.V * Nat.card (P.complement x) := hcard.symm
    _ ≤ Nat.card X * Nat.card X ^ 3 := by
      rw [P.card_eq x]
      exact Nat.mul_le_mul_left _ (by simpa only [hV] using hR)
    _ = Nat.card X ^ 4 := by ring

theorem primitive_order
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hstructure : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (hbase : HalasiMarotiSolubleIrreducibleCubeBound)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    [IsSolvable G] : Nat.card G ^ 3 ≤ 24 ^ (Nat.card X - 1) := by
  by_cases hn : Nat.card X < 45
  · exact bounded_primitive_order catalogue G X hn
  obtain ⟨D⟩ := hstructure G X
  cases D with
  | inl D =>
    let i : Fin D.factorCount := ⟨0, D.factorCount_pos⟩
    let f : finiteGroupSocle G →* D.Simple :=
      (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp
        D.socleEquiv.toMonoidHom
    have hf : Function.Surjective f := by
      intro s
      exact ⟨D.socleEquiv.symm (fun _ => s), by simp [f]⟩
    have hs : IsSolvable D.Simple := solvable_of_surjective hf
    exact (D.noncommutative ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩).elim
  | inr P =>
    calc
      Nat.card G ^ 3 ≤ (Nat.card X ^ 4) ^ 3 :=
        Nat.pow_le_pow_left (affine_order_le_fourth hbase G X P) _
      _ = Nat.card X ^ 12 := by ring
      _ ≤ 24 ^ (Nat.card X - 1) := polynomial_le_exponential _ (by omega)

end SymmetricSubgroupAsymptotics.SolublePermutationOrderProof
