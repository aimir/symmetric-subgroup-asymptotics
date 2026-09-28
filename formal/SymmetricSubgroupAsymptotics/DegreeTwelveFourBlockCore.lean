import SymmetricSubgroupAsymptotics.DegreeTwelveTopGeometry
import SymmetricSubgroupAsymptotics.BlockKernelSignCoordinates
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The original binary core after eliminating four-fibre signs

The saturated 4-by-3 branch has a nonzero original block-kernel head.
Once its literal fibre signs have been eliminated, the elements of the
original block kernel whose squares are one form a normal binary subgroup.
It embeds in the product of the three actual Klein groups, and the original
quotient is a 3-group. Schur--Zassenhaus supplies an actual complement.

Sign elimination itself, local fullness of this binary core, and the
faithful transitive action of the complement on the nine local translations
are not asserted here. In particular the core is not asserted to be the
whole V4^3, and this intermediate split is not called an earlier owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

omit [Finite Ω] in
/-- Saturation supplies a nonzero head in the actual original kernel
intersection, not merely a positive numerical chief weight. -/
theorem fourByThree_intersection_head_eq_one
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 (N ⊓ D.topMap.ker)) = 1 := by
  have hUpper := originalBlockChiefHead_bound D.map D.map_equivariant D.base
    (N ⊓ D.topMap.ker) inf_le_right c
  rw [hWeight, hPoints, ternaryIndexWidth_three] at hUpper
  have hUpperNat : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ D.topMap.ker)) ≤ 1 := by
    exact_mod_cast hUpper
  have hChain := primeRelativeHead_chain_le (N ⊓ D.topMap.ker) N 3 inf_le_left
  rw [primeRelativeHead_second_isomorphism,
    primeRelativeHead_original_range, hTop, hRank] at hChain
  omega

end OriginalMinimalBlock

namespace DegreeTwelveFourBlockCore

abbrev A4 := alternatingGroup (Fin 4)
abbrev V4 := alternatingGroup.kleinFour (Fin 4)

private theorem a4_pow_six (g : A4) : g ^ 6 = 1 := by
  decide +kernel +revert

private theorem a4_involution_mul (g h : A4) (hg : g ^ 2 = 1) (hh : h ^ 2 = 1) :
    (g * h) ^ 2 = 1 := by
  decide +kernel +revert

private theorem a4_involution_mem (g : A4) (hg : g ^ 2 = 1) : g ∈ V4 := by
  have hperm : (g.val : Equiv.Perm (Fin 4)) ^ 2 = 1 := congrArg Subtype.val hg
  have hd : orderOf g.val ∣ 2 ^ 1 := by
    simpa only [pow_one] using orderOf_dvd_of_pow_eq_one hperm
  have htypes := alternatingGroup.mem_kleinFour_of_order_two_pow
    (by simp : Nat.card (Fin 4) = 4) g.property hd
  rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
  rcases htypes with h | h
  · left
    exact Subtype.ext (Equiv.Perm.cycleType_eq_zero.mp h)
  · exact Or.inr h

section Coordinates

variable {G T I : Type*} [Group G] [Group T]
    (π : G →* T) (ρ : π.ker →* (I → A4)) (hρ : Function.Injective ρ)

include hρ in
private theorem kernel_pow_six (g : π.ker) : g ^ 6 = 1 := by
  apply hρ
  rw [map_pow, map_one]
  funext i
  exact a4_pow_six (ρ g i)

include hρ in
private theorem kernel_involution_mul (g h : π.ker)
    (hg : g ^ 2 = 1) (hh : h ^ 2 = 1) : (g * h) ^ 2 = 1 := by
  apply hρ
  rw [map_pow, map_mul, map_one]
  funext i
  apply a4_involution_mul
  · exact congrFun (by simpa only [map_pow, map_one] using congrArg ρ hg) i
  · exact congrFun (by simpa only [map_pow, map_one] using congrArg ρ hh) i

include ρ hρ in
/-- Intrinsic membership in the original group: no independent coordinates
or abstract replacement of the binary core is assumed. -/
def core : Subgroup G where
  carrier := {g | g ∈ π.ker ∧ g ^ 2 = 1}
  one_mem' := ⟨π.ker.one_mem, one_pow 2⟩
  mul_mem' := by
    rintro g h ⟨hg, hg2⟩ ⟨hh, hh2⟩
    refine ⟨π.ker.mul_mem hg hh, ?_⟩
    exact congrArg Subtype.val (kernel_involution_mul π ρ hρ
      (⟨g, hg⟩ : π.ker) (⟨h, hh⟩ : π.ker) (Subtype.ext hg2) (Subtype.ext hh2))
  inv_mem' := by
    rintro g ⟨hg, hg2⟩
    exact ⟨π.ker.inv_mem hg, by rw [inv_pow, hg2, inv_one]⟩

@[simp] theorem mem_core (g : G) : g ∈ core π ρ hρ ↔ g ∈ π.ker ∧ g ^ 2 = 1 := Iff.rfl

instance core_normal : (core π ρ hρ).Normal where
  conj_mem := by
    rintro g ⟨hg, hg2⟩ a
    exact ⟨Subgroup.Normal.conj_mem inferInstance g hg a,
      by rw [conj_pow, hg2, mul_one, mul_inv_cancel]⟩

theorem core_le_kernel : core π ρ hρ ≤ π.ker := fun _ h => h.1

theorem core_exponent_two (g : core π ρ hρ) : g ^ 2 = 1 :=
  Subtype.ext g.property.2

theorem core_isPGroup : IsPGroup 2 (core π ρ hρ) := by
  intro g
  exact ⟨1, by simpa only [pow_one] using core_exponent_two π ρ hρ g⟩

/-- Literal coordinates land in the same three Klein subgroups of A4. -/
def coreCoordinates : core π ρ hρ →* (I → V4) where
  toFun g i := ⟨ρ ⟨g.val, g.property.1⟩ i, a4_involution_mem _ (by
    have hpow : (⟨g.val, g.property.1⟩ : π.ker) ^ 2 = 1 := Subtype.ext g.property.2
    exact congrFun (by simpa only [map_pow, map_one] using congrArg ρ hpow) i)⟩
  map_one' := by
    funext i
    apply Subtype.ext
    exact congrFun ρ.map_one i
  map_mul' g h := by
    funext i
    apply Subtype.ext
    exact congrFun (ρ.map_mul ⟨g.val, g.property.1⟩ ⟨h.val, h.property.1⟩) i

theorem coreCoordinates_injective : Function.Injective (coreCoordinates π ρ hρ) := by
  intro g h he
  have hh : ρ ⟨g.val, g.property.1⟩ = ρ ⟨h.val, h.property.1⟩ := by
    funext i
    exact congrArg Subtype.val (congrFun he i)
  apply Subtype.ext
  exact congrArg (fun z : π.ker => (z : G)) (hρ hh)

theorem core_card_le [Finite I] : Nat.card (core π ρ hρ) ≤ 4 ^ Nat.card I := by
  have h := Nat.card_le_card_of_injective (coreCoordinates π ρ hρ)
    (coreCoordinates_injective π ρ hρ)
  have hv : Nat.card V4 = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  simpa only [Nat.card_fun, hv] using h

/-- With original top order three, every original quotient element has
ninth power one. This proves its 3-group property without a split premise. -/
theorem quotient_isPGroup [Finite G] (hTop : Nat.card π.range = 3) :
    IsPGroup 3 (G ⧸ core π ρ hρ) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (core π ρ hρ) q
  refine ⟨2, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hg3 : g ^ 3 ∈ π.ker := by
    change π (g ^ 3) = 1
    rw [map_pow]
    have h := pow_card_eq_one' (x := π.rangeRestrict g)
    rw [hTop] at h
    exact congrArg Subtype.val h
  refine ⟨?_, ?_⟩
  · change g ^ 9 ∈ π.ker
    rw [show 9 = 3 * 3 by omega, pow_mul]
    exact π.ker.pow_mem hg3 3
  · have h6 := congrArg Subtype.val
      (kernel_pow_six π ρ hρ (⟨g ^ 3, hg3⟩ : π.ker))
    change (g ^ 3) ^ 6 = 1 at h6
    change (g ^ 9) ^ 2 = 1
    simpa only [← pow_mul] using h6

/-- The complement is an actual subgroup of the original group. Its
exponent need not be three: the order81 owner is allowed. -/
theorem complement_exists [Finite G] (hTop : Nat.card π.range = 3) :
    ∃ P : Subgroup G, Subgroup.IsComplement' (core π ρ hρ) P ∧ IsPGroup 3 P := by
  have hb := core_isPGroup π ρ hρ
  have hq := quotient_isPGroup π ρ hρ hTop
  obtain ⟨u, hu⟩ := hb.exists_card_eq
  obtain ⟨v, hv⟩ := hq.exists_card_eq
  have hc : Nat.Coprime (Nat.card (core π ρ hρ)) (core π ρ hρ).index := by
    rw [hu, Subgroup.index_eq_card, hv]
    exact (Nat.Coprime.pow_left u (by decide : Nat.Coprime 2 3)).pow_right v
  obtain ⟨P, hP⟩ := Subgroup.exists_right_complement'_of_coprime hc
  exact ⟨P, hP, hq.of_equiv hP.symm.QuotientMulEquiv⟩

end Coordinates

section LiteralFibres

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x)

abbrev Kernel := OriginalBlockClassBound.Kernel (A := A) (X := X)

def fibreCoordinate (x : X) : Kernel (A := A) (X := X) →* Equiv.Perm (Fin 4) :=
  (e x).symm.permCongrHom.toMonoidHom.comp (OriginalBlockClassBound.coordinate b hb x)

/-- This is the remaining local sign condition, not a consequence asserted
merely from the chief-weight number one. -/
def AllEven : Prop := ∀ (x : X) (k : Kernel (A := A) (X := X)),
  fibreCoordinate b hb e x k ∈ alternatingGroup (Fin 4)

def alternatingCoordinates (hEven : AllEven b hb e) :
    Kernel (A := A) (X := X) →* (X → A4) where
  toFun k x := ⟨fibreCoordinate b hb e x k, hEven x k⟩
  map_one' := by funext x; exact Subtype.ext ((fibreCoordinate b hb e x).map_one)
  map_mul' k l := by funext x; exact Subtype.ext ((fibreCoordinate b hb e x).map_mul k l)

theorem alternatingCoordinates_injective [FaithfulSMul A Ω]
    (hEven : AllEven b hb e) : Function.Injective (alternatingCoordinates b hb e hEven) := by
  intro k l hkl
  apply OriginalBlockClassBound.coordinates_injective b hb
  funext x
  apply (e x).symm.permCongrHom.injective
  exact congrArg Subtype.val (congrFun hkl x)

/-- A bounded, fully original splitting consequence of actual sign
elimination. No identification of W with the whole product is made. -/
theorem binary_core_and_ternary_complement
    [Finite A] [FaithfulSMul A Ω] [Finite X]
    (hX : Nat.card X = 3)
    (hTop : Nat.card (MulAction.toPermHom A X).range = 3)
    (hEven : AllEven b hb e) :
    ∃ (W P : Subgroup A) (_ : W.Normal),
      (∀ a : A, a ∈ W ↔ a ∈ (MulAction.toPermHom A X).ker ∧ a ^ 2 = 1) ∧
      IsPGroup 2 W ∧ (∀ a : W, a ^ 2 = 1) ∧ Nat.card W ≤ 64 ∧
      (∃ φ : W →* (X → V4), Function.Injective φ) ∧ Subgroup.IsComplement' W P ∧ IsPGroup 3 P := by
  let π := MulAction.toPermHom A X
  let ρ := alternatingCoordinates b hb e hEven
  have hρ : Function.Injective ρ := alternatingCoordinates_injective b hb e hEven
  obtain ⟨P, hP, hP3⟩ := complement_exists π ρ hρ hTop
  refine ⟨core π ρ hρ, P, core_normal π ρ hρ, fun _ => Iff.rfl,
    core_isPGroup π ρ hρ, core_exponent_two π ρ hρ, ?_, ?_, hP, hP3⟩
  · simpa only [hX] using core_card_le π ρ hρ
  · exact ⟨coreCoordinates π ρ hρ, coreCoordinates_injective π ρ hρ⟩

end LiteralFibres

end DegreeTwelveFourBlockCore
end SymmetricSubgroupAsymptotics
