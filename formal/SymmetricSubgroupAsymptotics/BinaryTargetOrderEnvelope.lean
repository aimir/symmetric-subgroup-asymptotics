import SymmetricSubgroupAsymptotics.BinaryAbelianization
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Homomorphisms to an actual binary target, bounded by its order

A central order-two series in the target bounds all literal homomorphisms
from the SAME original source. Each nonempty fibre is injected into the
source's binary characters. Empty fibres and nonsplit extensions are allowed.
No generator-number theorem, permutation-rank bound, or class-count input
is used. The eventual marker cost is twice the base-two logarithm of the
actual target order; it need not satisfy every character-entry criterion.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

universe u v

local instance targetOrderHomFinite {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] : Finite (A →* B) :=
  Finite.of_injective (fun f : A →* B => (f : A → B)) DFunLike.coe_injective

section CentralFibre
variable {J Q : Type*} [Group J] [Group Q]
    (C : Subgroup Q) [C.Normal] (hC : C ≤ Subgroup.center Q)

private theorem centralHomDifference_mem (β : J →* Q ⧸ C)
    (f f₀ : {f : J →* Q // (QuotientGroup.mk' C).comp f = β}) (x : J) :
    f.1 x * (f₀.1 x)⁻¹ ∈ C := by
  apply (QuotientGroup.eq_one_iff (N := C) _).mp
  change QuotientGroup.mk' C (f.1 x * (f₀.1 x)⁻¹) = 1
  have hf : QuotientGroup.mk' C (f.1 x) = β x := DFunLike.congr_fun f.2 x
  have hf₀ : QuotientGroup.mk' C (f₀.1 x) = β x := DFunLike.congr_fun f₀.2 x
  rw [map_mul, map_inv, hf, hf₀, mul_inv_cancel]

/-- Differences use an origin only inside the actual fibre. Centrality
makes them homomorphisms into the literal central subgroup. -/
private def centralHomDifference (β : J →* Q ⧸ C)
    (f₀ f : {f : J →* Q // (QuotientGroup.mk' C).comp f = β}) : J →* C where
  toFun x := ⟨f.1 x * (f₀.1 x)⁻¹, centralHomDifference_mem C β f f₀ x⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, inv_one, mul_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    have hc : Commute (f₀.1 x) (f.1 y * (f₀.1 y)⁻¹) :=
      Subgroup.mem_center_iff.mp (hC (centralHomDifference_mem C β f f₀ y)) (f₀.1 x)
    change f.1 (x*y) * (f₀.1 (x*y))⁻¹ =
      (f.1 x * (f₀.1 x)⁻¹) * (f.1 y * (f₀.1 y)⁻¹)
    calc
      _ = (f.1 x * (f₀.1 x)⁻¹) *
          (f₀.1 x * (f.1 y * (f₀.1 y)⁻¹) * (f₀.1 x)⁻¹) := by
        rw [map_mul, map_mul]
        group
      _ = _ := by rw [hc.mul_inv_cancel]

include hC in
private theorem centralHomDifference_injective (β : J →* Q ⧸ C)
    (f₀ : {f : J →* Q // (QuotientGroup.mk' C).comp f = β}) :
    Function.Injective (centralHomDifference C hC β f₀) := by
  intro f g h
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  have he := congrArg Subtype.val (DFunLike.congr_fun h x)
  change f.1 x * (f₀.1 x)⁻¹ = g.1 x * (f₀.1 x)⁻¹ at he
  exact mul_right_cancel he

include hC in
/-- The central-extension estimate counts every original homomorphism.
It does not discard a translation factor or assume a split extension. -/
theorem binaryTargetOrder_centralHom_card_le [Finite J] [Finite Q] :
    Nat.card (J →* Q) ≤ Nat.card (J →* Q ⧸ C) * Nat.card (J →* C) := by
  classical
  letI := Fintype.ofFinite (J →* Q ⧸ C)
  have hfibre (β : J →* Q ⧸ C) :
      Nat.card {f : J →* Q // (QuotientGroup.mk' C).comp f = β} ≤
        Nat.card (J →* C) := by
    by_cases h : Nonempty {f : J →* Q // (QuotientGroup.mk' C).comp f = β}
    · obtain ⟨f₀⟩ := h
      exact Nat.card_le_card_of_injective _ (centralHomDifference_injective C hC β f₀)
    · letI := not_nonempty_iff.mp h
      simp
  calc
    _ = Nat.card (Σ β : J →* Q ⧸ C,
        {f : J →* Q // (QuotientGroup.mk' C).comp f = β}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv
        (fun f : J →* Q => (QuotientGroup.mk' C).comp f))).symm
    _ = ∑ β : J →* Q ⧸ C,
        Nat.card {f : J →* Q // (QuotientGroup.mk' C).comp f = β} := Nat.card_sigma
    _ ≤ ∑ _β : J →* Q ⧸ C, Nat.card (J →* C) :=
      Finset.sum_le_sum (fun β _ => hfibre β)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]
      rfl
end CentralFibre

/-- An original nontrivial finite 2-group has a literal central subgroup
of order two. Its centrality and cardinality are derived, not supplied. -/
theorem binaryTargetOrder_exists_central_two
    {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q] (hQ : IsPGroup 2 Q) :
    ∃ C : Subgroup Q, C ≤ Subgroup.center Q ∧ Nat.card C = 2 := by
  letI : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hZ := hQ.to_subgroup (Subgroup.center Q)
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center Q) := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨Subgroup.zpowers (z : Q), Subgroup.zpowers_le.mpr z.property, ?_⟩
  exact (Nat.card_zpowers (z : Q)).trans ((Subgroup.orderOf_coe z).trans hz)

/-- Explicit-order form: one binary character factor for each actual
central order-two step. The source is arbitrary, not necessarily a 2-group. -/
theorem binaryTargetOrder_hom_card_le_of_card_pow_two
    {J : Type u} [Group J] [Finite J] {Q : Type v} [Group Q] [Finite Q]
    (a : ℕ) (hcard : Nat.card Q = 2^a) :
    Nat.card (J →* Q) ≤ 2^(a * binaryCharacterRank J) := by
  classical
  have hmain : ∀ (a : ℕ) (R : Type v) [Group R] [Finite R],
      Nat.card R = 2^a → Nat.card (J →* R) ≤ 2^(a * binaryCharacterRank J) := by
    intro a
    induction a with
    | zero =>
      intro R _ _ hR
      letI : Subsingleton R := (Nat.card_eq_one_iff_unique.mp (by simpa using hR)).1
      letI : Subsingleton (J →* R) := ⟨fun f g => MonoidHom.ext (fun _ => Subsingleton.elim _ _)⟩
      simp
    | succ a ih =>
      intro R _ _ hR
      have hp : 0 < 2^a := pow_pos (by decide) a
      letI : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hR, pow_succ]
        omega)
      obtain ⟨C, hC, hc⟩ := binaryTargetOrder_exists_central_two (IsPGroup.of_card hR)
      letI : C.Normal := ⟨by
        intro c hc' r
        have hcomm : Commute r c := Subgroup.mem_center_iff.mp (hC hc') r
        rw [hcomm.mul_inv_cancel]
        exact hc'⟩
      have hquot : Nat.card (R ⧸ C) = 2^a := by
        have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup C
        rw [hR, hc, pow_succ] at hm
        omega
      let e : C ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hc (by simp)
      have hhom : Nat.card (J →* C) = 2^binaryCharacterRank J := by
        rw [Nat.card_congr (e.monoidHomCongrRightEquiv (M := J)),
          binaryAbelianizationGroupHom_card]
        simp only [Module.finrank_self, mul_one]
      calc
        _ ≤ Nat.card (J →* R ⧸ C) * Nat.card (J →* C) :=
          binaryTargetOrder_centralHom_card_le C hC
        _ ≤ 2^(a * binaryCharacterRank J) * 2^binaryCharacterRank J := by
          rw [hhom]
          exact Nat.mul_le_mul_right _ (ih (R ⧸ C) hquot)
        _ = 2^((a+1) * binaryCharacterRank J) := by
          rw [← pow_add, Nat.add_mul, one_mul]
  exact hmain a Q hcard

/-- Canonical target-order envelope. `Nat.log 2 (Nat.card Q)` is exact
because Q is an actual finite 2-group. -/
theorem binaryTargetOrder_hom_card_le
    {J Q : Type*} [Group J] [Finite J] [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) :
    Nat.card (J →* Q) ≤ 2^(Nat.log 2 (Nat.card Q) * binaryCharacterRank J) := by
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  have hlog : Nat.log 2 (Nat.card Q) = a := by
    rw [ha, Nat.log_pow (by decide)]
  rw [hlog]
  exact binaryTargetOrder_hom_card_le_of_card_pow_two a ha

/-- Arbitrary surviving literal onto maps are a subset of the original
Hom space. The bound counts maps, with no quotient by target automorphisms. -/
theorem binaryTargetOrder_surviving_epi_card_le
    {J Q : Type*} [Group J] [Finite J] [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (S : {f : J →* Q // Function.Surjective f} → Prop) :
    Nat.card {f : {f : J →* Q // Function.Surjective f} // S f} ≤
      2^(Nat.log 2 (Nat.card Q) * binaryCharacterRank J) := by
  exact (Nat.card_le_card_of_injective (fun f => f.1.1)
    (fun _ _ h => Subtype.ext (Subtype.ext h))).trans (binaryTargetOrder_hom_card_le hQ)

end SymmetricSubgroupAsymptotics
