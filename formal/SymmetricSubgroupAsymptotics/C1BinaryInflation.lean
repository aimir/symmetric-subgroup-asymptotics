import SymmetricSubgroupAsymptotics.C1SplitCharacters
import Mathlib.GroupTheory.PGroup

/-!
# Binary-kernel inflation of actual split ternary characters

An elementary power argument lifts the order-three witness through any
binary kernel. It preserves the complete character space, the nonsplit
annihilator, and arbitrary literal surviving predicates.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G H : Type*} [Group G] [Group H]

def ternaryInflation (π : G →* H) :
    PrimeCharacters 3 H →ₗ[ZMod 3] PrimeCharacters 3 G where
  toFun χ := χ.comp π.toAdditive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ternaryInflation_apply (π : G →* H) (χ : PrimeCharacters 3 H) (x : G) :
    ternaryInflation π χ (Additive.ofMul x) = χ (Additive.ofMul (π x)) := rfl

/-- Every original ternary character kills the actual binary kernel. -/
theorem ternaryCharacter_kills_binary_kernel (π : G →* H) (hπ : IsPGroup 2 π.ker)
    (χ : PrimeCharacters 3 G) (x : G) (hx : x ∈ π.ker) : χ (Additive.ofMul x) = 0 := by
  obtain ⟨k,hk⟩ := hπ (⟨x,hx⟩ : π.ker)
  have hp : x^(2^k) = 1 := congrArg Subtype.val hk
  have hc := congrArg (fun z : G => χ (Additive.ofMul z)) hp
  change χ ((2^k) • Additive.ofMul x) = χ 0 at hc
  rw [map_nsmul,map_zero,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hc
  exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by decide : (2 : ZMod 3) ≠ 0))

/-- Actual inflation is a linear equivalence, with no chosen splitting of π. -/
def ternaryBinaryInflationEquiv (π : G →* H) (hs : Function.Surjective π)
    (hπ : IsPGroup 2 π.ker) : PrimeCharacters 3 H ≃ₗ[ZMod 3] PrimeCharacters 3 G :=
  LinearEquiv.ofBijective (ternaryInflation π) ⟨by
    intro χ ψ h
    apply AddMonoidHom.ext
    intro y
    obtain ⟨x,hx⟩ := hs y.toMul
    have he := DFunLike.congr_fun h (Additive.ofMul x)
    simpa only [ternaryInflation_apply,hx] using he, by
    intro χ
    have hp : Function.Surjective π.toAdditive := hs
    let χ' := π.toAdditive.liftOfSurjective hp
      ⟨χ,fun x hx => ternaryCharacter_kills_binary_kernel π hπ χ x.toMul hx⟩
    refine ⟨χ',?_⟩
    apply AddMonoidHom.ext
    intro x
    exact AddMonoidHom.liftOfRightInverse_comp_apply π.toAdditive
      (Function.surjInv hp) (Function.rightInverse_surjInv hp)
      ⟨χ,fun x hx => ternaryCharacter_kills_binary_kernel π hπ χ x.toMul hx⟩ x⟩

/-- Binary-kernel inflation preserves actual sections. The reverse
direction lifts a finite-order element by removing its binary part. -/
theorem ternaryBinaryInflation_split_iff (π : G →* H) (hs : Function.Surjective π)
    (hπ : IsPGroup 2 π.ker) (χ : PrimeCharacters 3 H) :
    TernarySplit (ternaryInflation π χ) ↔ TernarySplit χ := by
  constructor
  · intro h
    obtain ⟨x,hx,hχ⟩ := (ternarySplit_iff_witness _).mp h
    apply (ternarySplit_iff_witness χ).mpr
    refine ⟨π x,?_,hχ⟩
    apply orderOf_eq_prime
    · rw [← map_pow,← hx,pow_orderOf_eq_one,map_one]
    · intro he
      have hval : χ (Additive.ofMul (π x)) = 1 := hχ
      simp [he] at hval
  · intro h
    obtain ⟨y,hy,hχ⟩ := (ternarySplit_iff_witness χ).mp h
    obtain ⟨x,hx⟩ := hs y
    have hx3 : x^3 ∈ π.ker := by
      change π (x^3) = 1
      rw [map_pow,hx,← hy,pow_orderOf_eq_one]
    obtain ⟨k,hk⟩ := hπ (⟨x^3,hx3⟩ : π.ker)
    have hp : (x^3)^(2^k) = 1 := congrArg Subtype.val hk
    have hz : (x^(2^k))^3 = 1 := by simpa only [← pow_mul,Nat.mul_comm] using hp
    have hv : ternaryInflation π χ (Additive.ofMul (x^(2^k))) = (2 : ZMod 3)^k := by
      change χ (Additive.ofMul (π (x^(2^k)))) = _
      rw [map_pow,hx]
      change χ ((2^k) • Additive.ofMul y) = _
      rw [map_nsmul,hχ,nsmul_eq_mul,mul_one,Nat.cast_pow,Nat.cast_ofNat]
    have hv0 : (2 : ZMod 3)^k ≠ 0 := pow_ne_zero _ (by decide)
    have hxne : x^(2^k) ≠ 1 := by
      intro he
      rw [he] at hv
      exact hv0 (by simpa using hv.symm)
    have hord : orderOf (x^(2^k)) = 3 := orderOf_eq_prime hz hxne
    by_contra hn
    have hzero := (ternaryNonsplitAnnihilator_mem_iff _).mpr hn
    exact hv0 (hv.symm.trans (hzero _ hord))

/-- The original nonsplit annihilator is transported exactly, not merely
bounded by an ambient space having a convenient dimension. -/
def ternaryBinaryNonsplitEquiv (π : G →* H) (hs : Function.Surjective π)
    (hπ : IsPGroup 2 π.ker) :
    ternaryNonsplitAnnihilator H ≃ₗ[ZMod 3] ternaryNonsplitAnnihilator G where
  toFun χ := ⟨ternaryInflation π χ.1, by
    rw [ternaryNonsplitAnnihilator_mem_iff,ternaryBinaryInflation_split_iff π hs hπ]
    exact (ternaryNonsplitAnnihilator_mem_iff χ.1).mp χ.2⟩
  invFun χ := ⟨(ternaryBinaryInflationEquiv π hs hπ).symm χ.1,by
    rw [ternaryNonsplitAnnihilator_mem_iff]
    have hn := (ternaryNonsplitAnnihilator_mem_iff χ.1).mp χ.2
    have he := ternaryBinaryInflation_split_iff π hs hπ
      ((ternaryBinaryInflationEquiv π hs hπ).symm χ.1)
    rw [show ternaryInflation π ((ternaryBinaryInflationEquiv π hs hπ).symm χ.1)=χ.1 from
      (ternaryBinaryInflationEquiv π hs hπ).apply_symm_apply _] at he
    exact fun h => hn (he.mpr h)⟩
  left_inv χ := Subtype.ext ((ternaryBinaryInflationEquiv π hs hπ).symm_apply_apply χ.1)
  right_inv χ := Subtype.ext ((ternaryBinaryInflationEquiv π hs hπ).apply_symm_apply χ.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ternaryBinaryInflation_ranks (π : G →* H) (hs : Function.Surjective π)
    (hπ : IsPGroup 2 π.ker) :
    ternaryCharacterRank H = ternaryCharacterRank G ∧
      ternaryNonsplitRank H = ternaryNonsplitRank G :=
  ⟨(ternaryBinaryInflationEquiv π hs hπ).finrank_eq,
    (ternaryBinaryNonsplitEquiv π hs hπ).finrank_eq⟩

/-- Arbitrary survival exclusions are pulled back literally through the
same inflation equivalence. No equality with the unrestricted count is used. -/
theorem ternaryBinaryInflation_surviving_weight (π : G →* H) (hs : Function.Surjective π)
    (hπ : IsPGroup 2 π.ker) (S : PrimeCharacters 3 G → Prop) :
    ternarySurvivingWeight (fun χ => S (ternaryInflation π χ)) = ternarySurvivingWeight S := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (ternaryBinaryInflationEquiv π hs hπ).toEquiv ?_
  intro χ
  exact and_congr_left (fun _ => (ternaryBinaryInflation_split_iff π hs hπ χ).symm)

end SymmetricSubgroupAsymptotics
