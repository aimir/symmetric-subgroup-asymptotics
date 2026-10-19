import SymmetricSubgroupAsymptotics.NaturalFourNonbinaryQuotientBinaryImage
import SymmetricSubgroupAsymptotics.CubicNormalImageNorm

/-! The genuine cubic action is fixed-point-free on the actual binary
normal image in every nonbinary natural S4 quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NaturalFourCubicNormalImage

private theorem klein_norm : ∀ a : Equiv.Perm (Fin 4), a^3=1 → a≠1 →
    ∀ v : Equiv.Perm (Fin 4), v∈NaturalS4.klein →
      v*(a*v*a⁻¹)*(a^2*v*(a^2)⁻¹)=1 := by decide +kernel

theorem fixed_eq_one {Q : Type} [Group Q] [Finite Q]
    (f : Equiv.Perm (Fin 4) →* Q) (hf : Function.Surjective f)
    (hQ : 3∣Nat.card Q) (L : Subgroup Q) (hL : L.Normal)
    (hb : IsPGroup 2 L) (a : Equiv.Perm (Fin 4)) (ha : a^3=1) (hne : a≠1)
    (x : Q) (hx : x∈L) (hfix : f a*x*(f a)⁻¹=x) : x=1 :=
  CubicNormalImageNorm.fixed_eq_one f hf NaturalS4.klein L
    (NaturalFourNonbinaryQuotientBinaryImage.symmetric_preimage_le f hf hQ L hL hb)
    a (fun v hv => NaturalS4.kleinSet_sq v hv) (klein_norm a ha hne) x hx hfix

theorem card_le_four {Q : Type} [Group Q] [Finite Q]
    (f : Equiv.Perm (Fin 4) →* Q) (hf : Function.Surjective f)
    (hQ : 3∣Nat.card Q) (L : Subgroup Q) (hL : L.Normal)
    (hb : IsPGroup 2 L) : Nat.card L≤4 := by
  have h := CubicNormalImageNorm.card_le f hf NaturalS4.klein L
    (NaturalFourNonbinaryQuotientBinaryImage.symmetric_preimage_le f hf hQ L hL hb)
  simpa only [NaturalS4.card_klein] using h

private theorem double_transposition_mem : ∀ v : Equiv.Perm (Fin 4),
    v.cycleType={2,2} → v∈NaturalS4.klein := by decide +kernel

private theorem alternating_klein_mem (v : alternatingGroup (Fin 4))
    (hv : v∈alternatingGroup.kleinFour (Fin 4)) : v.val∈NaturalS4.klein := by
  rw [← SetLike.mem_coe,alternatingGroup.coe_kleinFour_of_card_eq_four (by simp),
    Set.mem_union,Set.mem_singleton_iff,Set.mem_setOf_eq] at hv
  rcases hv with hv | hv
  · rw [hv]; exact NaturalS4.klein.one_mem
  · exact double_transposition_mem v.val hv

private theorem alternating_klein_norm : ∀ a : alternatingGroup (Fin 4),
    a^3=1 → a≠1 → ∀ v : alternatingGroup (Fin 4),
      v∈alternatingGroup.kleinFour (Fin 4) →
      v*(a*v*a⁻¹)*(a^2*v*(a^2)⁻¹)=1 := by
  intro a ha hn v hv
  apply Subtype.ext
  apply klein_norm a.val
  · simpa only [Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val ha
  · intro he; exact hn (Subtype.ext he)
  · exact alternating_klein_mem v hv

private theorem alternating_klein_square : ∀ v : alternatingGroup (Fin 4),
    v∈alternatingGroup.kleinFour (Fin 4) → v^2=1 := by
  intro v hv
  apply Subtype.ext
  exact NaturalS4.kleinSet_sq v.val (alternating_klein_mem v hv)

theorem alternating_fixed_eq_one {Q : Type} [Group Q] [Finite Q]
    (f : alternatingGroup (Fin 4) →* Q) (hf : Function.Surjective f)
    (hQ : 3∣Nat.card Q) (L : Subgroup Q) (hL : L.Normal)
    (hb : IsPGroup 2 L) (a : alternatingGroup (Fin 4)) (ha : a^3=1) (hne : a≠1)
    (x : Q) (hx : x∈L) (hfix : f a*x*(f a)⁻¹=x) : x=1 :=
  CubicNormalImageNorm.fixed_eq_one f hf (alternatingGroup.kleinFour (Fin 4)) L
    (NaturalFourNonbinaryQuotientBinaryImage.alternating_preimage_le f hf hQ L hL hb)
    a alternating_klein_square (alternating_klein_norm a ha hne) x hx hfix

theorem alternating_card_le_four {Q : Type} [Group Q] [Finite Q]
    (f : alternatingGroup (Fin 4) →* Q) (hf : Function.Surjective f)
    (hQ : 3∣Nat.card Q) (L : Subgroup Q) (hL : L.Normal)
    (hb : IsPGroup 2 L) : Nat.card L≤4 := by
  have h := CubicNormalImageNorm.card_le f hf (alternatingGroup.kleinFour (Fin 4)) L
    (NaturalFourNonbinaryQuotientBinaryImage.alternating_preimage_le f hf hQ L hL hb)
  simpa only [alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)] using h

end SymmetricSubgroupAsymptotics.NaturalFourCubicNormalImage
