import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Small fixed-degree additive owners: the formal instances

This file instantiates the small additive template for the historical
families whose complete fixed-source estimates are proved formally here.

* DIH (D0379): an actual faithful transitive action of the dihedral group
  `D_{2ℓ}`, `ℓ` an odd prime, of degree `ℓ` or `2ℓ`, excluding the natural
  degrees three and five.  The onto maps to `D_{2ℓ}` are controlled by one
  character of the derived subgroup of the source, and every other literal
  quotient has order at most two:
  `Z_J(U) ≤ (|Aut D_{2ℓ}| + 2) 3^(b/3)`.
* SAPRIM, regular prime row (D0387): the regular cyclic group of prime
  order `p` with `7 ≤ p < 1024`.  Its literal quotients are `C_p` and `1`:
  `Z_J(U) ≤ 2 · 3^(b/3)`.

Both use Kovács--Praeger's abelian quotient bound and the tail slope
`log₂ 3 / 3`, which meets the cold gap at every width at least six.

The other rows of the small additive menu have no source in this particular
dispatcher.  Natural S4, A4W2, LIN and TF are proved in their dedicated
modules and joined to DIH and the regular-prime SAPRIM row by
`Non2PreE7SmallAdditiveNumericalInstances`.  The still-open historical rows
are:

* SAPRIM, other rows: `d₅(J) ≤ b/5` (regular `C₅`, natural `D₁₀`),
  the `H¹` bound for binary primitive affine modules, and the abelian
  and prime-power rows;
* INV12all: the joint `d₂`/`d₃` proper-`V₄`-base estimate;
* S3EXC: the constants of `B₃(s, H)`;
* S3TWO, S3CYCL and S3SYL: literal normal-menu certificates of their
  degree `8`, `9` and `12` classes;
* 5EXC: the comparator-list moment.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

/-! ## Dihedral groups of odd prime degree -/

section Dihedral

open DihedralGroup

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem zmod_two_ne_zero_of_ne_two (h2 : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have hdvd : ℓ ∣ 2 := by
    exact (ZMod.natCast_eq_zero_iff 2 ℓ).mp (by exact_mod_cast h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact hℓ.out.one_lt.ne' h1
  · exact h2 h1

/-- The reflection sign. -/
def dihedralSign : DihedralGroup ℓ →* Multiplicative (ZMod 2) where
  toFun x := match x with
    | r _ => 1
    | sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;> (simp; try rfl)

/-- The rotation index. -/
def rotationIndex : DihedralGroup ℓ → ZMod ℓ
  | r i => i
  | sr i => i

theorem mem_commutator_dihedral (h2 : ℓ ≠ 2) (x : DihedralGroup ℓ) :
    x ∈ commutator (DihedralGroup ℓ) ↔ ∃ i, x = r i := by
  constructor
  · intro hx
    have hker := Abelianization.commutator_subset_ker (dihedralSign (ℓ := ℓ)) hx
    rw [MonoidHom.mem_ker] at hker
    cases x with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      exact absurd hker (by
        change ¬ (Multiplicative.ofAdd (1 : ZMod 2) = 1)
        decide)
  · rintro ⟨i, rfl⟩
    have hc : r (-2 : ZMod ℓ) ∈ commutator (DihedralGroup ℓ) := by
      have hmem := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (sr (0 : ZMod ℓ))) (Subgroup.mem_top (r (1 : ZMod ℓ)))
      have heq : ⁅sr (0 : ZMod ℓ), r (1 : ZMod ℓ)⁆ = r (-2 : ZMod ℓ) := by
        rw [commutatorElement_def]
        simp only [inv_sr, inv_r, sr_mul_r, sr_mul_sr, r_mul_r]
        congr 1
        ring
      rw [← commutator_def] at hmem
      rwa [heq] at hmem
    have h2' : (-2 : ZMod ℓ) ≠ 0 := neg_ne_zero.mpr (zmod_two_ne_zero_of_ne_two h2)
    haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    let k : ℕ := (i * (-2 : ZMod ℓ)⁻¹).val
    have hk : r (-2 : ZMod ℓ) ^ k = r i := by
      rw [r_pow]
      congr 1
      simp only [k, ZMod.natCast_zmod_val]
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ h2', mul_one]
    rw [← hk]
    exact Subgroup.pow_mem _ hc k

/-- The rotation character on the derived subgroup. -/
def dihedralDerivedCharacter (h2 : ℓ ≠ 2) :
    commutator (DihedralGroup ℓ) →* Multiplicative (ZMod ℓ) where
  toFun x := Multiplicative.ofAdd (rotationIndex x.1)
  map_one' := rfl
  map_mul' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := (mem_commutator_dihedral h2 x).mp hx
    obtain ⟨j, rfl⟩ := (mem_commutator_dihedral h2 y).mp hy
    rfl

/-- The derived cyclic-dual data of `D_{2ℓ}`. -/
def dihedralDerivedCyclicDual (h2 : ℓ ≠ 2) :
    DerivedCyclicDual (DihedralGroup ℓ) ℓ where
  character := dihedralDerivedCharacter h2
  self_centralizing := by
    intro q hq
    cases q with
    | r i => exact (mem_commutator_dihedral h2 _).mpr ⟨i, rfl⟩
    | sr j =>
      exfalso
      have hmem : r (1 : ZMod ℓ) ∈ commutator (DihedralGroup ℓ) :=
        (mem_commutator_dihedral h2 _).mpr ⟨1, rfl⟩
      have h := hq ⟨r 1, hmem⟩
      simp only [sr_mul_r, r_mul_sr, sr.injEq] at h
      apply zmod_two_ne_zero_of_ne_two h2
      linear_combination h
  no_fixed := by
    rintro ⟨a, ha⟩ hfix
    obtain ⟨i, rfl⟩ := (mem_commutator_dihedral h2 a).mp ha
    have h := hfix (sr 0)
    simp only [sr_mul_r, inv_sr, sr_mul_sr, r.injEq] at h
    apply Subtype.ext
    change r i = r 0
    congr 1
    have h2i : (2 : ZMod ℓ) * i = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2i with h0 | h0
    · exact absurd h0 (zmod_two_ne_zero_of_ne_two h2)
    · exact h0
  separating := by
    rintro ⟨a, ha⟩ hsep
    obtain ⟨i, rfl⟩ := (mem_commutator_dihedral h2 a).mp ha
    have h := hsep 1
    apply Subtype.ext
    change r i = r 0
    have h' : Multiplicative.ofAdd i = Multiplicative.ofAdd (0 : ZMod ℓ) := by
      simpa [dihedralDerivedCharacter, rotationIndex] using h
    rw [Multiplicative.ofAdd.injective h']

/-- A nontrivial normal subgroup of `D_{2ℓ}` contains every rotation. -/
theorem rotation_mem_of_normal_ne_bot (h2 : ℓ ≠ 2) (N : Subgroup (DihedralGroup ℓ))
    (hN : N.Normal) (hne : N ≠ ⊥) (j : ZMod ℓ) : r j ∈ N := by
  obtain ⟨⟨n, hnN⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  -- a nontrivial rotation in `N`
  obtain ⟨i, hi, hiN⟩ : ∃ i : ZMod ℓ, i ≠ 0 ∧ r i ∈ N := by
    cases n with
    | r i =>
      refine ⟨i, fun h0 => hn1 ?_, hnN⟩
      apply Subtype.ext
      change r i = r 0
      rw [h0]
    | sr i =>
      have hconj := hN.conj_mem _ hnN (r 1)
      have hprod := N.mul_mem hnN hconj
      simp only [inv_r, r_mul_sr, sr_mul_r, sr_mul_sr] at hprod
      refine ⟨(i - 1 + -1 - i : ZMod ℓ), ?_, hprod⟩
      have : (i - 1 + -1 - i : ZMod ℓ) = -2 := by ring
      rw [this]
      exact neg_ne_zero.mpr (zmod_two_ne_zero_of_ne_two h2)
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  let k : ℕ := (j * i⁻¹).val
  have hk : r i ^ k = r j := by
    rw [r_pow]
    congr 1
    simp only [k, ZMod.natCast_zmod_val]
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hi, mul_one]
  rw [← hk]
  exact N.pow_mem hiN k

/-- Nontrivial normal quotients of `D_{2ℓ}` have order at most two. -/
theorem card_quotient_le_two_of_ne_bot (h2 : ℓ ≠ 2) (N : Subgroup (DihedralGroup ℓ))
    [hN : N.Normal] (hne : N ≠ ⊥) : Nat.card (DihedralGroup ℓ ⧸ N) ≤ 2 := by
  have hNcard : ℓ ≤ Nat.card N := by
    have hinj : Function.Injective (fun i : ZMod ℓ =>
        (⟨r i, rotation_mem_of_normal_ne_bot h2 N hN hne i⟩ : N)) := by
      intro i j h
      have := congrArg Subtype.val h
      simpa using this
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_zmod] at this
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [DihedralGroup.nat_card] at hmul
  have hℓpos : 0 < ℓ := hℓ.out.pos
  by_contra hlt
  push Not at hlt
  have h3 : 3 * ℓ ≤ Nat.card (DihedralGroup ℓ ⧸ N) * Nat.card N :=
    Nat.mul_le_mul (by omega) hNcard
  rw [← hmul] at h3
  omega

end Dihedral

/-- `3^(b/3) = 2^((log₂ 3 / 3) b)`. -/
theorem three_rpow_third_eq (b : ℕ) :
    (3 : ℝ) ^ ((b : ℝ) / 3) = (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  rw [show (Real.logb 2 3 / 3) * (b : ℝ) = Real.logb 2 3 * ((b : ℝ) / 3) by ring,
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by norm_num)]

/-- `1/2 ≤ log₂ 3 / 3`, since `2^3 ≤ 3^2`. -/
theorem half_le_logThreeThird : (1 / 2 : ℝ) ≤ Real.logb 2 3 / 3 := by
  have h : (3 / 2 : ℝ) ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    have h1 : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) ≤ (3 : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h1
  linarith

namespace Non2UnipotentPrefixFiniteMenu

/-! ## Family source shapes -/

/-- DIH: an actual faithful transitive action of `D_{2ℓ}`, `ℓ` an odd
prime, of degree `ℓ` or `2ℓ`, excluding the natural degrees three and
five. -/
structure PreE7DihSource (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  ℓ : ℕ
  prime : ℓ.Prime
  odd : ℓ ≠ 2
  equiv : preE7NonPairAction w i ≃* DihedralGroup ℓ
  degree : w = ℓ ∨ w = 2 * ℓ
  not_natural_small : 6 ≤ w

/-- SAPRIM, regular prime row: the regular cyclic group of prime order
`7 ≤ p < 1024`. -/
structure PreE7SaprimRegularPrimeSource (w : ℕ) (i : PreE7NonPairActionClass w) :
    Type where
  p : ℕ
  prime : p.Prime
  seven_le : 7 ≤ p
  lt_bound : p < 1024
  equiv : preE7NonPairAction w i ≃* Multiplicative (ZMod p)
  degree : w = p

/-! ## The dihedral instance -/

namespace PreE7DihSource

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7DihSource w i)

/-- The fixed certificate on one literal normal axis. -/
def axis (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N PUnit
      (Real.logb 2 3 / 3) := by
  haveI : Fact S.ℓ.Prime := ⟨S.prime⟩
  by_cases hN : N.1 = ⊥
  · refine .tail (Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* DihedralGroup S.ℓ :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot.trans S.equiv)
    have hcongr : Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) =
        Nat.card (GroupEpimorphism J (DihedralGroup S.ℓ)) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
    have hD := (dihedralDerivedCyclicDual (ℓ := S.ℓ) S.odd).epi_card_le (J := J)
    have hHom := cyclicCharacter_card_le_abelianization (commutator J) S.ℓ
    have hKPJ := derived_abelianization_le hKP J
    rw [hcongr]
    calc (Nat.card (GroupEpimorphism J (DihedralGroup S.ℓ)) : ℝ)
        ≤ (Nat.card (commutator J →* Multiplicative (ZMod S.ℓ)) : ℝ) *
            Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) := by exact_mod_cast hD
      _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) *
            Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact (by exact_mod_cast hHom : (Nat.card (commutator J →*
            Multiplicative (ZMod S.ℓ)) : ℝ) ≤ Nat.card (Abelianization (commutator J))).trans
            hKPJ
      _ = _ := by rw [three_rpow_third_eq, mul_comm]
  · refine .tail 1 zero_le_one ?_
    intro b J
    let M : Subgroup (DihedralGroup S.ℓ) := N.1.map S.equiv.toMonoidHom
    haveI : M.Normal := Subgroup.Normal.map N.2 _ S.equiv.surjective
    have hM : M ≠ ⊥ := by
      intro h
      apply hN
      rw [eq_bot_iff]
      intro x hx
      have : S.equiv x ∈ M := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
      exact (Subgroup.mem_bot).mpr this
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* (DihedralGroup S.ℓ ⧸ M) :=
      QuotientGroup.congr N.1 M S.equiv rfl
    have hcard : Nat.card (preE7NonPairAction w i ⧸ N.1) ≤ 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_quotient_le_two_of_ne_bot S.odd M hM
    calc (Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) : ℝ)
        ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * b) :=
          groupEpimorphism_card_le_of_card_le_two J hcard
      _ ≤ 1 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
          rw [one_mul]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_right half_le_logThreeThird (Nat.cast_nonneg b))

/-- The template data of a DIH source. -/
def toData (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveData w i where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := Real.logb 2 3 / 3
  comparator_window := trivialSmallComparatorWindow S.not_natural_small
  tail_window := logThreeThird_le_window S.not_natural_small
  axis := S.axis hKP

end PreE7DihSource

/-! ## The regular prime instance -/

namespace PreE7SaprimRegularPrimeSource

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7SaprimRegularPrimeSource w i)

include S in
theorem width_ge_six : 6 ≤ w := by
  have := S.seven_le
  have := S.degree
  omega

/-- The fixed certificate on one literal normal axis. -/
def axis (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N PUnit
      (Real.logb 2 3 / 3) := by
  haveI : Fact S.p.Prime := ⟨S.prime⟩
  refine .tail 1 zero_le_one ?_
  intro b J
  have hcard : Nat.card (preE7NonPairAction w i) = S.p := by
    rw [Nat.card_congr S.equiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
  haveI : Fact (Nat.card (preE7NonPairAction w i)).Prime := ⟨hcard ▸ S.prime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card N.1 with hbot | htop
  · let e : (preE7NonPairAction w i ⧸ N.1) ≃* Multiplicative (ZMod S.p) :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans
        (QuotientGroup.quotientBot.trans S.equiv)
    have hcongr : Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) =
        Nat.card (GroupEpimorphism J (Multiplicative (ZMod S.p))) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
    have hepi : Nat.card (GroupEpimorphism J (Multiplicative (ZMod S.p))) ≤
        Nat.card (J →* Multiplicative (ZMod S.p)) := by
      letI : Finite (J →* Multiplicative (ZMod S.p)) := Finite.of_injective
        (fun f : J →* Multiplicative (ZMod S.p) => (f : J → Multiplicative (ZMod S.p)))
        DFunLike.coe_injective
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hHom := cyclicCharacter_card_le_abelianization J S.p
    rw [hcongr, one_mul, ← three_rpow_third_eq]
    exact (by exact_mod_cast hepi.trans hHom :
      (Nat.card (GroupEpimorphism J (Multiplicative (ZMod S.p))) : ℝ) ≤
        Nat.card (Abelianization J)).trans (hKP b J)
  · haveI : Subsingleton (preE7NonPairAction w i ⧸ N.1) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) :=
      ⟨fun f g => Subtype.ext (MonoidHom.ext fun _ => Subsingleton.elim _ _)⟩
    have hle : Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    calc (Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) : ℝ) ≤ 1 := by
          exact_mod_cast hle
      _ ≤ 1 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
          rw [one_mul]
          exact Real.one_le_rpow (by norm_num)
            (mul_nonneg (div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
              (by norm_num)) (Nat.cast_nonneg b))

/-- The template data of a regular prime source. -/
def toData (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveData w i where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := Real.logb 2 3 / 3
  comparator_window := trivialSmallComparatorWindow S.width_ge_six
  tail_window := logThreeThird_le_window S.width_ge_six
  axis := S.axis hKP

end PreE7SaprimRegularPrimeSource

/-! ## The dispatcher -/

/-- The certified source data of each small additive family.  Families whose
modes are not yet certified formally have no source. -/
def PreE7SmallAdditiveSourceData :
    PreE7NoPairNoC3EarlierOwnerFamily → ∀ w, PreE7NonPairActionClass w → Type
  | .dih => fun w i => PreE7DihSource w i
  | .saprim => fun w i => PreE7SaprimRegularPrimeSource w i
  | _ => fun _ _ => PEmpty

/-- The template data underlying a small additive source. -/
def PreE7SmallAdditiveSourceData.toData (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) {w : ℕ}
    {i : PreE7NonPairActionClass w} (S : PreE7SmallAdditiveSourceData family w i) :
    PreE7SmallAdditiveData w i := by
  cases family
  all_goals first
    | exact PEmpty.elim S
    | skip
  case dih => exact PreE7DihSource.toData S hKP
  case saprim => exact PreE7SaprimRegularPrimeSource.toData S hKP

/-- The dispatcher into the mixed local catalogue. -/
theorem preE7_smallAdditiveLocalFamilyAction (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) (w : ℕ)
    (i : PreE7NonPairActionClass w) (S : PreE7SmallAdditiveSourceData family w i) :
    preE7NoPairNoC3EarlierLocalFamilyAction family w i :=
  (S.toData hKP family).localFamilyAction family

/-- Every dispatched certificate meets the transfer parameters and the cold
tail gap at `ρ = 1/8192`. -/
theorem preE7_smallAdditive_entryParameters (hKP : KovacsPraegerAbelianizationBound)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) (w : ℕ)
    (i : PreE7NonPairActionClass w) (S : PreE7SmallAdditiveSourceData family w i) :
    PreE7CharacterEntryParameters preE7CharacterRho w
      ((S.toData hKP family).certificate family).v
      ((S.toData hKP family).certificate family).eta
      ((S.toData hKP family).certificate family).delta
      ((S.toData hKP family).certificate family).cutoff
      ((S.toData hKP family).certificate family).alpha
      ((S.toData hKP family).certificate family).theta :=
  (S.toData hKP family).entryParameters family

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
