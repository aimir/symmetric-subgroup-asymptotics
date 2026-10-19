import SymmetricSubgroupAsymptotics.NaturalFourCubicNormalImage
import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOrder

/-! Transport of the actual nonbinary quotient image theorem through
the faithful quartet top. The acting cubic and quotient denominator are
transported along the same displayed group equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulCubicNormalImage
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)

def Property (B : Type) [Group B] : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (f : B →* Q), Function.Surjective f →
    3∣Nat.card Q → ∀ (L : Subgroup Q), L.Normal → IsPGroup 2 L →
      Nat.card L≤4 ∧ ∀ (a : B), a^3=1 → a≠1 → ∀ x∈L,
        f a*x*(f a)⁻¹=x → x=1

theorem transport {B D : Type} [Group B] [Group D]
    (e : B ≃* D) (h : Property D) : Property B := by
  intro Q _ _ f hf hQ L hL hb
  let f' := f.comp e.symm.toMonoidHom
  obtain ⟨hc,hfix⟩ := h Q f' (hf.comp e.symm.surjective) hQ L hL hb
  refine ⟨hc,?_⟩
  intro a ha hn x hx hh
  have hcub : (e a)^3=1 := by rw [← map_pow,ha,map_one]
  have hne : e a≠1 := by
    intro he
    apply hn
    apply e.injective
    simpa only [map_one] using he
  apply hfix (e a) hcub hne x hx
  simpa only [f',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using hh

theorem above_alternating (B : Subgroup (Equiv.Perm (Fin 4)))
    (hB : alternatingGroup (Fin 4)≤B) : Property B := by
  rcases AlternatingTopImageNormalGenerators.above_alternating B hB with hb | hb
  · subst B
    intro Q _ _ f hf hQ L hL hbin
    refine ⟨NaturalFourCubicNormalImage.alternating_card_le_four f hf hQ L hL hbin,?_⟩
    exact NaturalFourCubicNormalImage.alternating_fixed_eq_one f hf hQ L hL hbin
  · subst B
    apply transport Subgroup.topEquiv
    intro Q _ _ f hf hQ L hL hbin
    refine ⟨NaturalFourCubicNormalImage.card_le_four f hf hQ L hL hbin,?_⟩
    exact NaturalFourCubicNormalImage.fixed_eq_one f hf hQ L hL hbin

theorem property (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    Property C := by
  let e : C ≃* (top C).range := MulEquiv.ofBijective (top C).rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h),(top C).rangeRestrict_surjective⟩
  apply transport e
  apply above_alternating
  intro p hp
  exact heven ⟨p,hp⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulCubicNormalImage
