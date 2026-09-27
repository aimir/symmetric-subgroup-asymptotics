import SymmetricSubgroupAsymptotics.PGroupProductClassBound
import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation

/-! The original kernel of an equivariant block map embeds through its
actions on all literal fibres. Class bounds for those actual coordinate
subgroups combine multiplicatively, preserving all kernel correlations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The class extension bound with the quotient identified with the actual
image of the original homomorphism. -/
theorem conjugacyClass_card_le_kernel_mul_range
    {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) :
    Nat.card (ConjClasses G) ≤
      Nat.card (ConjClasses f.ker) * Nat.card (ConjClasses f.range) := by
  letI : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let e := QuotientGroup.quotientKerEquivRange f
  have hq : Nat.card (ConjClasses (G ⧸ f.ker)) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (conjugacyClass_card_le_normal_mul_quotient f.ker).trans
    (Nat.mul_le_mul_left _ hq)

namespace OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)

abbrev topMap : A →* Equiv.Perm X := MulAction.toPermHom A X
abbrev Kernel : Subgroup A := (topMap (A := A) (X := X)).ker
abbrev Top : Subgroup (Equiv.Perm X) := (topMap (A := A) (X := X)).range

/-- Restriction of the original block kernel to one literal original fibre. -/
def coordinate (x : X) : Kernel (A := A) (X := X) →*
    Equiv.Perm (originalBlockFibre b x) :=
  (originalBlockFibreAction b hb x).comp
    (blockKernelToStabilizer x (Kernel (A := A) (X := X)) le_rfl)

theorem coordinate_apply (x : X) (k : Kernel (A := A) (X := X))
    (ω : originalBlockFibre b x) :
    ((coordinate b hb x k ω : originalBlockFibre b x) : Ω) = (k : A) • ω.1 := rfl

/-- The literal fibre containing a point detects the original kernel's
action there. No transitivity or independence of fibre actions is required. -/
theorem coordinates_injective [FaithfulSMul A Ω] :
    Function.Injective (fun k x => coordinate b hb x k) := by
  intro k l h
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := Ω)
  intro ω
  let v : originalBlockFibre b (b ω) := ⟨ω, rfl⟩
  exact congrArg (fun σ : Equiv.Perm (originalBlockFibre b (b ω)) => (σ v : Ω))
    (congrFun h (b ω))

include hb in
theorem kernel_class_card_le_product [Finite A] [Finite Ω] [Fintype X]
    [FaithfulSMul A Ω] (p : ℕ) (hA : IsPGroup p A) (c : X → ℕ)
    (hc : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      IsPGroup p L → Nat.card (ConjClasses L) ≤ c x) :
    Nat.card (ConjClasses (Kernel (A := A) (X := X))) ≤ ∏ x, c x :=
  pGroup_conjugacyClass_card_le_finite_coordinate_bounds p
    (fun x => Equiv.Perm (originalBlockFibre b x)) c hc
    (Kernel (A := A) (X := X)) (hA.to_subgroup _)
    (coordinate b hb) (coordinates_injective b hb)

include hb in
theorem kernel_class_card_le_power [Finite A] [Finite Ω] [Finite X]
    [FaithfulSMul A Ω] (p : ℕ) (hA : IsPGroup p A) (c : ℕ)
    (hc : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      IsPGroup p L → Nat.card (ConjClasses L) ≤ c) :
    Nat.card (ConjClasses (Kernel (A := A) (X := X))) ≤ c ^ Nat.card X := by
  letI : Fintype X := Fintype.ofFinite _
  simpa only [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card] using
    kernel_class_card_le_product b hb p hA (fun _ => c) hc

include hb in
/-- The resulting actual block recurrence, with the original kernel and
the faithful original top image. Its local class bounds remain explicit. -/
theorem class_card_le_power_mul_top [Finite A] [Finite Ω] [Finite X]
    [FaithfulSMul A Ω] (p : ℕ) (hA : IsPGroup p A) (c : ℕ)
    (hc : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre b x))),
      IsPGroup p L → Nat.card (ConjClasses L) ≤ c) :
    Nat.card (ConjClasses A) ≤ c ^ Nat.card X *
      Nat.card (ConjClasses (Top (A := A) (X := X))) :=
  (conjugacyClass_card_le_kernel_mul_range (topMap (A := A) (X := X))).trans
    (Nat.mul_le_mul_right _ (kernel_class_card_le_power b hb p hA c hc))

end OriginalBlockClassBound
end SymmetricSubgroupAsymptotics

end
