import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseMass
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import SymmetricSubgroupAsymptotics.PrimeElementaryEpimorphismBound
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Uniform epimorphism bounds for every actual quotient of the natural A4 top

The original quotient map is retained throughout.  Its literal kernel is
    normal in `A4`, hence is `bot`, the Klein four, or `top`.  The latter two
    cases are already controlled by the internal permutation-character theorem:
the target is respectively cyclic of order three or trivial.

The full-`A4` estimate is proved here from one explicit binary character on
the literal derived subgroup.  Equal labels determine equal epimorphism
kernels; the existing kernel-label theorem and permutation half-rank bound
then give exponent `1 / 2`.  This embeds directly into `8 / 15`, and the
result is installed through every original normal axis without an external
numerical top-map premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

open TernaryA4InvariantSubmodules

private abbrev A4Klein : Subgroup A4 :=
  alternatingGroup.kleinFour (Fin 4)

private theorem normal_card_two_le_center
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center G := by
  obtain ⟨u, hu, hu_unique⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hx1 : x = 1
  · simp [hx1]
  let xN : N := ⟨x, hx⟩
  let gxN : N :=
    ⟨g * x * g⁻¹, Subgroup.Normal.conj_mem (inferInstance : N.Normal) x hx g⟩
  have hxN_ne : xN ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  have hgxN_ne : gxN ≠ 1 := by
    intro h
    have hval : g * x * g⁻¹ = 1 := congrArg Subtype.val h
    apply hx1
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hval]; simp
  have hconj : g * x * g⁻¹ = x := by
    exact congrArg Subtype.val ((hu_unique gxN hgxN_ne).trans (hu_unique xN hxN_ne).symm)
  calc
    g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [hconj]

/-- A generic compatibility interface for a coupled full-`A4` estimate.
The internal derived-character theorem below proves this interface and then
uses its stronger bound directly, without the displayed polynomial factor. -/
def A4CoupledFullTopEpiInput (C : ℝ) : Prop :=
  ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
      C * ((b : ℝ) + 1) * (2 : ℝ) ^ (b / 2)

private def permBitValue (v : Equiv.Perm (Fin 4)) : ZMod 2 :=
  if (v 0).val < 2 then 0 else 1

private theorem permBitValue_mul_of_klein (x y : Equiv.Perm (Fin 4))
    (hx : x = 1 ∨ x.cycleType = {2, 2})
    (hy : y = 1 ∨ y.cycleType = {2, 2}) :
    permBitValue (x * y) = permBitValue x + permBitValue y := by
  revert x y
  decide

private theorem permBitValue_commutator_detects (v : Equiv.Perm (Fin 4))
    (hv : Equiv.Perm.sign v = 1)
    (h : ∀ a : Equiv.Perm (Fin 4), Equiv.Perm.sign a = 1 →
      permBitValue ⁅v, a⁆ = 0) : v = 1 := by
  revert v
  decide

private def k4BitMul : A4Klein →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (permBitValue (v : Equiv.Perm (Fin 4)))
  map_one' := by decide
  map_mul' := by
    intro x y
    apply congrArg Multiplicative.ofAdd
    apply permBitValue_mul_of_klein
    · have hx := x.property
      rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)] at hx
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
      exact hx.imp (fun h ↦ congrArg Subtype.val h) id
    · have hy := y.property
      rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)] at hy
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hy
      exact hy.imp (fun h ↦ congrArg Subtype.val h) id

private def k4Bit : PrimeCharacters 2 A4Klein := k4BitMul.toAdditive

private def a4CommutatorElement (v a : A4) : A4Klein :=
  ⟨⁅v, a⁆, by
    change ⁅v, a⁆ ∈ alternatingGroup.kleinFour (Fin 4)
    rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top a)⟩

private theorem k4Bit_detects (v : A4)
    (h : ∀ a : A4, k4Bit (Additive.ofMul (a4CommutatorElement v a)) = 0) :
    v = 1 := by
  apply Subtype.ext
  apply permBitValue_commutator_detects v (Equiv.Perm.mem_alternatingGroup.mp v.property)
  intro a ha
  let a' : A4 := ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩
  simpa [k4Bit, k4BitMul, a4CommutatorElement] using h a'

private abbrev Derived (J : Type*) [Group J] := commutator J

private def a4DerivedRestriction {J : Type*} [Group J]
    (f : GroupEpimorphism J A4) : Derived J →* A4Klein where
  toFun x := ⟨f.1 x, by
    change f.1 x ∈ alternatingGroup.kleinFour (Fin 4)
    rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
    have hx : f.1 x ∈ (commutator J).map f.1 := Subgroup.mem_map_of_mem f.1 x.property
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.2, ← commutator_def] at hx
    exact hx⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private def a4DerivedLabel {J : Type*} [Group J]
    (f : GroupEpimorphism J A4) : PrimeCharacters 2 (Derived J) :=
  k4Bit.comp (a4DerivedRestriction f).toAdditive

private theorem a4DerivedLabel_kernel {J : Type*} [Group J]
    (f g : GroupEpimorphism J A4) (h : a4DerivedLabel f = a4DerivedLabel g) :
    f.1.ker = g.1.ker := by
  ext x
  constructor
  · intro hx
    change g.1 x = 1
    apply k4Bit_detects
    intro a
    obtain ⟨y, rfl⟩ := g.2 a
    let z : Derived J := ⟨⁅x, y⁆, by
      change ⁅x, y⁆ ∈ commutator J
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
    have hz := DFunLike.congr_fun h (Additive.ofMul z)
    have hfx : f.1 x = 1 := hx
    have hfz : k4Bit (Additive.ofMul (a4DerivedRestriction f z)) = 0 := by
      simp [z, a4DerivedRestriction, map_commutatorElement, hfx]
      exact k4Bit.map_zero
    have hgz : k4Bit (Additive.ofMul (a4DerivedRestriction g z)) = 0 := by
      exact hz.symm.trans hfz
    simpa [z, a4DerivedRestriction, a4CommutatorElement,
      map_commutatorElement] using hgz
  · intro hx
    change f.1 x = 1
    apply k4Bit_detects
    intro a
    obtain ⟨y, rfl⟩ := f.2 a
    let z : Derived J := ⟨⁅x, y⁆, by
      change ⁅x, y⁆ ∈ commutator J
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
    have hz := DFunLike.congr_fun h (Additive.ofMul z)
    have hgx : g.1 x = 1 := hx
    have hgz : k4Bit (Additive.ofMul (a4DerivedRestriction g z)) = 0 := by
      simp [z, a4DerivedRestriction, map_commutatorElement, hgx]
      exact k4Bit.map_zero
    have hfz : k4Bit (Additive.ofMul (a4DerivedRestriction f z)) = 0 := by
      exact hz.trans hgz
    simpa [z, a4DerivedRestriction, a4CommutatorElement,
      map_commutatorElement] using hfz

theorem a4_epimorphism_card_le_derived_character
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J A4) ≤
      2 ^ (b / 2) * Nat.card (A4 ≃* A4) := by
  have hlabel : Nat.card (GroupEpimorphism J A4) ≤
      Nat.card (PrimeCharacters 2 (Derived J)) * Nat.card (A4 ≃* A4) :=
    groupEpimorphism_card_le_kernel_labels a4DerivedLabel a4DerivedLabel_kernel
  have hrank : Module.finrank (ZMod 2) (PrimeCharacters 2 (Derived J)) ≤ b / 2 := by
    simpa only [Nat.card_fin] using
      permutation_binaryCharacterRank_le_half (Derived J) (Fin b)
  calc
    Nat.card (GroupEpimorphism J A4) ≤
        Nat.card (PrimeCharacters 2 (Derived J)) * Nat.card (A4 ≃* A4) := hlabel
    _ = 2 ^ Module.finrank (ZMod 2) (PrimeCharacters 2 (Derived J)) *
          Nat.card (A4 ≃* A4) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ ≤ 2 ^ (b / 2) * Nat.card (A4 ≃* A4) := by
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank)

/-- The full natural `A4` top is controlled internally by one binary
character on the literal derived subgroup.  No independent sum over
ternary top maps or semisimple type decomposition is needed. -/
theorem a4CoupledFullTopEpi_internal :
    A4CoupledFullTopEpiInput (Nat.card (A4 ≃* A4) : ℝ) := by
  intro b J
  have hnat := a4_epimorphism_card_le_derived_character b J
  have hcast : (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
      (2 : ℝ) ^ (b / 2) * Nat.card (A4 ≃* A4) := by
    exact_mod_cast hnat
  calc
    (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
        (2 : ℝ) ^ (b / 2) * Nat.card (A4 ≃* A4) := hcast
    _ ≤ (Nat.card (A4 ≃* A4) : ℝ) * ((b : ℝ) + 1) *
          (2 : ℝ) ^ (b / 2) := by
      have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      have hb : (1 : ℝ) ≤ (b : ℝ) + 1 := by linarith
      have hA : (0 : ℝ) ≤ (Nat.card (A4 ≃* A4) : ℝ) := Nat.cast_nonneg _
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (b / 2) := by positivity
      nlinarith

/-- The literal normal subgroups of the natural four-point alternating
group.  This is a finite calculation on the displayed action, not an
abstract quotient classification premise. -/
private theorem a4_normal_subgroup_trichotomy :
    ∀ N : Subgroup A4, N.Normal →
      N = ⊥ ∨ N = A4Klein ∨ N = ⊤ := by
  intro N hnormal
  letI : N.Normal := hnormal
  have hcardA4 : Nat.card A4 = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hdvd : Nat.card N ∣ 12 := by
    simpa only [hcardA4] using N.card_subgroup_dvd_card
  have hcases : Nat.card N = 1 ∨ Nat.card N = 2 ∨ Nat.card N = 3 ∨
      Nat.card N = 4 ∨ Nat.card N = 6 ∨ Nat.card N = 12 := by
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      by_contra hc0
      have : c = 0 := Nat.eq_zero_of_not_pos hc0
      subst c
      simp at hc
    have hcle : c ≤ 12 := by
      nlinarith
    interval_cases c <;> omega
  rcases hcases with hN | hN | hN | hN | hN | hN
  · exact Or.inl (N.eq_bot_of_card_eq hN)
  · have hcenter : N ≤ Subgroup.center A4 := normal_card_two_le_center N hN
    have hcenterBot : Subgroup.center A4 = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hbot : N = ⊥ := by
      apply le_antisymm
      · simpa only [hcenterBot] using hcenter
      · exact bot_le
    exact (by rw [hbot] at hN; norm_num at hN)
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardA4, hN] at hmul
    have hqcard : Nat.card (A4 ⧸ N) = 4 := by omega
    have hcommQ : IsMulCommutative (A4 ⧸ N) :=
      ⟨⟨fun a b ↦ IsPGroup.commutative_of_card_eq_prime_sq (p := 2)
        (by simpa using hqcard) a b⟩⟩
    have hcomm : commutator A4 ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hKN : A4Klein ≤ N := by
      change alternatingGroup.kleinFour (Fin 4) ≤ N
      rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact hcomm
    have hdiv : 4 ∣ 3 := by
      have hd := Subgroup.card_dvd_of_le hKN
      change Nat.card (alternatingGroup.kleinFour (Fin 4)) ∣ Nat.card N at hd
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hN] at hd
      exact hd
    norm_num at hdiv
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardA4, hN] at hmul
    have hqcard : Nat.card (A4 ⧸ N) = 3 := by omega
    have hcommQ : IsMulCommutative (A4 ⧸ N) :=
      (isCyclic_of_prime_card hqcard).isMulCommutative
    have hcomm : commutator A4 ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hKN : A4Klein ≤ N := by
      change alternatingGroup.kleinFour (Fin 4) ≤ N
      rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact hcomm
    exact Or.inr (Or.inl (Subgroup.eq_of_le_of_card_ge hKN (by
      change Nat.card N ≤ Nat.card (alternatingGroup.kleinFour (Fin 4))
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hN])).symm)
  · have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardA4, hN] at hmul
    have hqcard : Nat.card (A4 ⧸ N) = 2 := by omega
    have hcommQ : IsMulCommutative (A4 ⧸ N) :=
      (isCyclic_of_prime_card hqcard).isMulCommutative
    have hcomm : commutator A4 ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hKN : A4Klein ≤ N := by
      change alternatingGroup.kleinFour (Fin 4) ≤ N
      rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact hcomm
    have hdiv : 4 ∣ 6 := by
      have hd := Subgroup.card_dvd_of_le hKN
      change Nat.card (alternatingGroup.kleinFour (Fin 4)) ∣ Nat.card N at hd
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hN] at hd
      exact hd
    norm_num at hdiv
  · exact Or.inr (Or.inr (N.eq_top_of_card_eq (hN.trans hcardA4.symm)))

private theorem a4_quotient_klein_card : Nat.card (A4 ⧸ A4Klein) = 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup A4Klein
  rw [alternatingGroup.card_of_card_eq_four (by simp),
    alternatingGroup.kleinFour_card_of_card_eq_four (by simp)] at h
  omega

/-- The polynomial loss in the coupled full-top estimate fits uniformly
inside the gap between `1 / 2` and `8 / 15`.  The constant `30` comes from
writing `b = 30 q + r` and using `q + 1 ≤ 2^q`. -/
theorem a4Coupled_polynomial_absorption (b : ℕ) :
    ((b : ℝ) + 1) * (2 : ℝ) ^ (b / 2) ≤
      30 * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
  let q := b / 30
  have hqpow : q + 1 ≤ 2 ^ q :=
    Nat.add_one_le_iff.mpr q.lt_two_pow_self
  have hbq : b + 1 ≤ 30 * (q + 1) := by
    dsimp only [q]
    omega
  have hpolyNat : b + 1 ≤ 30 * 2 ^ q :=
    hbq.trans (Nat.mul_le_mul_left 30 hqpow)
  have hpoly : (b : ℝ) + 1 ≤
      30 * (2 : ℝ) ^ (((1 : ℝ) / 30) * b) := by
    have hqNat : 30 * q ≤ b := by
      dsimp only [q]
      simpa only [mul_comm] using Nat.div_mul_le_self b 30
    have hq : (q : ℝ) ≤ ((1 : ℝ) / 30) * b := by
      have hq' : (30 : ℝ) * q ≤ b := by exact_mod_cast hqNat
      linarith
    calc
      (b : ℝ) + 1 ≤ 30 * (2 : ℝ) ^ q := by exact_mod_cast hpolyNat
      _ = 30 * (2 : ℝ) ^ (q : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ 30 * (2 : ℝ) ^ (((1 : ℝ) / 30) * b) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq) (by norm_num)
  have hhalfNat : 2 * (b / 2) ≤ b := by
    simpa only [mul_comm] using Nat.div_mul_le_self b 2
  have hhalf : (2 : ℝ) ^ (b / 2) ≤
      (2 : ℝ) ^ (((1 : ℝ) / 2) * b) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hhalf' : (2 : ℝ) * ((b / 2 : ℕ) : ℝ) ≤ b := by
      exact_mod_cast hhalfNat
    linarith
  calc
    ((b : ℝ) + 1) * (2 : ℝ) ^ (b / 2) ≤
        (30 * (2 : ℝ) ^ (((1 : ℝ) / 30) * b)) *
          (2 : ℝ) ^ (b / 2) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ ≤ (30 * (2 : ℝ) ^ (((1 : ℝ) / 30) * b)) *
          (2 : ℝ) ^ (((1 : ℝ) / 2) * b) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = 30 * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

private theorem a4_full_target_bound
    (C : ℝ) (hC : 0 ≤ C) (hfull : A4CoupledFullTopEpiInput C)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    {S : Type} [Group S] [Finite S]
    (q : A4QuotientMap S) (hker : q.1.ker = ⊥) :
    (Nat.card (GroupEpimorphism J S) : ℝ) ≤
      (30 * C) * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
  let e : A4 ≃* S := MulEquiv.ofBijective q.1
    ⟨(MonoidHom.ker_eq_bot_iff q.1).mp hker, q.2⟩
  rw [← fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
  calc
    (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
        C * ((b : ℝ) + 1) * (2 : ℝ) ^ (b / 2) := hfull b J
    _ ≤ C * (30 * (2 : ℝ) ^ (((8 : ℝ) / 15) * b)) :=
      by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (a4Coupled_polynomial_absorption b) hC
    _ = (30 * C) * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by ring

private theorem a4_klein_target_bound
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    {S : Type} [Group S] [Finite S]
    (q : A4QuotientMap S) (hker : q.1.ker = A4Klein) :
    (Nat.card (GroupEpimorphism J S) : ℝ) ≤
      (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
  have hcardS : Nat.card S = 3 := by
    calc
      Nat.card S = Nat.card (A4 ⧸ q.1.ker) :=
        (Nat.card_congr
          (QuotientGroup.quotientKerEquivOfSurjective q.1 q.2).toEquiv).symm
      _ = Nat.card (A4 ⧸ A4Klein) := by rw [hker]
      _ = 3 := a4_quotient_klein_card
  have hcardT : Nat.card TernaryCyclic = 3 := by
    simp [TernaryCyclic, Nat.card_eq_fintype_card]
  let e : S ≃* TernaryCyclic := mulEquivOfPrimeCardEq hcardS hcardT
  have hepi := groupEpimorphism_card_le_elementary 3 (G := J) e
  have hrank := permutation_ternaryCharacterRank_le_third J (Fin b)
  have hcount : Nat.card (GroupEpimorphism J S) ≤ 3 ^ (b / 3) := by
    apply hepi.trans
    apply Nat.pow_le_pow_right (by decide : 0 < 3)
    simpa using hrank
  have hcount' : (Nat.card (GroupEpimorphism J S) : ℝ) ≤
      (3 : ℝ) ^ (b / 3) := by exact_mod_cast hcount
  exact hcount'.trans (ternaryPower_le_primeBase_eight_fifteenths b (b / 3) (by omega))

private theorem a4_trivial_target_card
    {J S : Type} [Group J] [Group S] [Finite J] [Finite S]
    (q : A4QuotientMap S) (hker : q.1.ker = ⊤) :
    Nat.card (GroupEpimorphism J S) = 1 := by
  have hq : q.1 = 1 := MonoidHom.ker_eq_top_iff.mp hker
  have hS : Subsingleton S := by
    constructor
    intro x y
    obtain ⟨a, rfl⟩ := q.2 x
    obtain ⟨c, rfl⟩ := q.2 y
    simp only [hq, MonoidHom.one_apply]
  letI : Subsingleton S := hS
  letI : Subsingleton (GroupEpimorphism J S) :=
    ⟨fun f g => Subtype.ext (MonoidHom.ext fun _ => Subsingleton.elim _ _)⟩
  have hnonempty : Nonempty (GroupEpimorphism J S) :=
    ⟨⟨1, fun s => ⟨1, Subsingleton.elim _ _⟩⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hnonempty⟩

/-- A single coupled estimate for the full `A4` target proves the requested
degree-six exponent simultaneously for every actual quotient of the literal
natural top.  The output constant is universal in `b`, `J`, `S`, and the
chosen quotient map. -/
theorem a4QuotientTopEpiInput_of_coupled_full
    (C : ℝ) (hC : 0 ≤ C) (hfull : A4CoupledFullTopEpiInput C)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    {S : Type} [Group S] [Finite S]
    (q : A4QuotientMap S) :
    A4QuotientTopEpiInput b J S (max 1 (30 * C)) := by
  have hnormal : q.1.ker.Normal := inferInstance
  rcases a4_normal_subgroup_trichotomy q.1.ker hnormal with
      hker | hker | hker
  · have h := a4_full_target_bound C hC hfull b J q hker
    have hscale :
        (30 * C) * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) ≤
          max 1 (30 * C) * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 (30 * C)) (by positivity)
    exact h.trans hscale
  · have h := a4_klein_target_bound b J q hker
    have hscale :
        (2 : ℝ) ^ (((8 : ℝ) / 15) * b) ≤
          max 1 (30 * C) * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) :=
      by simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (le_max_left 1 (30 * C)) (by positivity))
    exact h.trans hscale
  · rw [A4QuotientTopEpiInput, a4_trivial_target_card q hker, Nat.cast_one]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
      apply Real.one_le_rpow (by norm_num)
      positivity
    have hscale :
        (2 : ℝ) ^ (((8 : ℝ) / 15) * b) ≤
          max 1 (30 * C) * (2 : ℝ) ^ (((8 : ℝ) / 15) * b) :=
      by simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (le_max_left 1 (30 * C)) (by positivity))
    exact hpow.trans hscale

/-- The checked derived-character theorem removes the coupled full-top
premise altogether.  Its stronger `1 / 2` exponent fits directly inside
`8 / 15`, so the internal result does not pay the polynomial-absorption
factor `30`. -/
theorem a4QuotientTopEpiInput_internal
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    {S : Type} [Group S] [Finite S]
    (q : A4QuotientMap S) :
    A4QuotientTopEpiInput b J S
      (max 1 (Nat.card (A4 ≃* A4) : ℝ)) := by
  have hnormal : q.1.ker.Normal := inferInstance
  rcases a4_normal_subgroup_trichotomy q.1.ker hnormal with
      hker | hker | hker
  · let e : A4 ≃* S := MulEquiv.ofBijective q.1
      ⟨(MonoidHom.ker_eq_bot_iff q.1).mp hker, q.2⟩
    rw [A4QuotientTopEpiInput, ← fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    have hnat := a4_epimorphism_card_le_derived_character b J
    have hcast : (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
        (2 : ℝ) ^ (b / 2) * Nat.card (A4 ≃* A4) := by
      exact_mod_cast hnat
    have hhalfNat : 2 * (b / 2) ≤ b := by
      simpa only [mul_comm] using Nat.div_mul_le_self b 2
    have hhalf : ((b / 2 : ℕ) : ℝ) ≤ ((8 : ℝ) / 15) * b := by
      have hhalf' : (2 : ℝ) * ((b / 2 : ℕ) : ℝ) ≤ b := by
        exact_mod_cast hhalfNat
      have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      linarith
    have hpow : (2 : ℝ) ^ (b / 2) ≤
        (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf
    calc
      (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
          (2 : ℝ) ^ (b / 2) * Nat.card (A4 ≃* A4) := hcast
      _ ≤ (2 : ℝ) ^ (((8 : ℝ) / 15) * b) * Nat.card (A4 ≃* A4) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ ≤ max 1 (Nat.card (A4 ≃* A4) : ℝ) *
          (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
        have hp : 0 ≤ (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by positivity
        have hA : (Nat.card (A4 ≃* A4) : ℝ) ≤
            max 1 (Nat.card (A4 ≃* A4) : ℝ) := le_max_right _ _
        nlinarith
  · have h := a4_klein_target_bound b J q hker
    exact h.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (le_max_left 1 (Nat.card (A4 ≃* A4) : ℝ)) (by positivity))
  · rw [A4QuotientTopEpiInput, a4_trivial_target_card q hker, Nat.cast_one]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (((8 : ℝ) / 15) * b) := by
      apply Real.one_le_rpow (by norm_num)
      positivity
    exact hpow.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (le_max_left 1 (Nat.card (A4 ≃* A4) : ℝ)) (by positivity))

/-- The degree-twelve prime-base physical owner now has no numerical
top-map premise.  Every original normal axis uses its literal descended
`A4` quotient map and the internally proved uniform constant. -/
theorem C1TernaryPrimeBaseOwnerWitness.physical_owner_bound_internal_top
    (U : Subgroup (Equiv.Perm (Fin 12)))
    (W : C1TernaryPrimeBaseOwnerWitness U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + 12) ≤
      c1EarlierKernel b .degreeTwelve
        (∑ N : {N : Subgroup U // N.Normal},
          (originalNormalRegularConstant 3 W.top W.baseModule W.baseChart N : ℝ) *
            max 1 (Nat.card (A4 ≃* A4) : ℝ))
        (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 12)))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  apply C1TernaryPrimeBaseOwnerWitness.physical_owner_bound_of_numerical_inputs
    U W b P hP
    (fun _ ↦ max 1 (Nat.card (A4 ≃* A4) : ℝ))
    (fun _ ↦ by positivity)
  intro J N
  letI : N.1.Normal := N.2
  exact a4QuotientTopEpiInput_internal b J
    (W.originalNormalA4QuotientMap N.1)

end SymmetricSubgroupAsymptotics

end
