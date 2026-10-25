import SymmetricSubgroupAsymptotics.LargeSmallFibreSubgroupClassGap
import Mathlib.GroupTheory.IsSubnormal

/-! Subnormal top class budgets for the SAME original block action.
The actual top of a subnormal source subgroup is identified with its
image under the original surjective top map. This retains correlations
and uses no class-number monotonicity for subgroup inclusions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
open OriginalBlockClassBound

theorem subnormal_class_card_le_power_mul_top_budget
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : ℕ) (hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      Nat.card (ConjClasses L) ≤ c)
    (d : ℕ) (hTop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ d)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ c ^ Nat.card X * d := by
  letI : Fintype X := Fintype.ofFinite _
  have hbH : ∀ (g : H) (ω : Ω), b (g • ω) = g • b ω := fun g ω => hb g.val ω
  have hrec := PermutationBlockClassReduction.class_card_le_product_mul_top
    b hbH (fun _ => c) hlocal
  have hrec' : Nat.card (ConjClasses H) ≤ c ^ Nat.card X *
      Nat.card (ConjClasses (Top (A := H) (X := X))) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hrec
  let f : A →* Top (A := A) (X := X) := (topMap (A := A) (X := X)).rangeRestrict
  let M : Subgroup (Top (A := A) (X := X)) := H.map f
  have hM : M.IsSubnormal := hH.map (MonoidHom.rangeRestrict_surjective _)
  have hr : M.map (Top (A := A) (X := X)).subtype = Top (A := H) (X := X) := by
    ext σ
    constructor
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨g,hg,he⟩ := hu
      exact ⟨⟨g,hg⟩,congrArg Subtype.val he⟩
    · rintro ⟨g,rfl⟩
      exact ⟨f g.val,⟨g.val,g.property,rfl⟩,rfl⟩
  let e := (M.equivMapOfInjective (Top (A := A) (X := X)).subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr hr)
  have ht : Nat.card (ConjClasses (Top (A := H) (X := X))) ≤ d :=
    (Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)).trans (hTop M hM)
  exact hrec'.trans (Nat.mul_le_mul_left _ ht)

end SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
