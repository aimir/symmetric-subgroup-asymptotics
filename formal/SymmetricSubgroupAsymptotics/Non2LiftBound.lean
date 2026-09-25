import SymmetricSubgroupAsymptotics.InflationRestriction

/-!
# Numerical lift bounds with the original extension retained

A module chart identifies the original abelian kernel and its conjugation
action. It does not split the extension. The bound applies to any literal
survival predicate on lifts above the same fixed quotient map.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open groupCohomology

universe u
variable {k J Q B : Type u} [CommRing k] [Group J] [Group Q] [Group B]

/-- A chart on the actual kernel, with its original quotient action.
This is structural action data, not a splitting or counting premise. -/
structure OriginalKernelModuleChart (π : Q →* B) (A : Rep k B) where
  equiv : Multiplicative A ≃* π.ker
  conjugate : ∀ (q : Q) (a : A),
    (equiv (Multiplicative.ofAdd (A.ρ (π q) a)) : Q) =
      q * (equiv (Multiplicative.ofAdd a) : Q) * q⁻¹

theorem originalKernelChart_add (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (a b : A) :
    (E.equiv (Multiplicative.ofAdd (a+b)) : Q) =
      (E.equiv (Multiplicative.ofAdd a) : Q) *
      (E.equiv (Multiplicative.ofAdd b) : Q) :=
  congrArg Subtype.val (E.equiv.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

/-- The original multiplicative kernel cocycles are the actual additive
cocycles of the pulled-back module action. -/
def originalKernelCocycleEquiv (π : Q →* B) (β : J →* B)
    (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (f₀ : HomomorphicLift π β) :
    KernelCocycle π f₀.1 ≃ cocycles₁ (quotientPullbackRep β A) where
  toFun z := ⟨fun j ↦ (E.equiv.symm (z.1 j)).toAdd, by
    apply (mem_cocycles₁_iff _).mpr
    intro x y
    change (E.equiv.symm (z.1 (x*y))).toAdd =
      A.ρ (β x) (E.equiv.symm (z.1 y)).toAdd + (E.equiv.symm (z.1 x)).toAdd
    rw [add_comm]
    apply Multiplicative.ofAdd.injective
    apply E.equiv.injective
    apply Subtype.val_injective
    rw [originalKernelChart_add]
    have ha := E.conjugate (f₀.1 x) (E.equiv.symm (z.1 y)).toAdd
    rw [homomorphicLift_above π β f₀ x] at ha
    rw [ha]
    change (E.equiv (E.equiv.symm (z.1 (x*y))) : Q) =
      (E.equiv (E.equiv.symm (z.1 x)) : Q) *
        (f₀.1 x * (E.equiv (E.equiv.symm (z.1 y)) : Q) * (f₀.1 x)⁻¹)
    simp only [MulEquiv.apply_symm_apply]
    exact (z.2 x y).trans (by group)⟩
  invFun z := ⟨fun j ↦ E.equiv (Multiplicative.ofAdd (z j)), by
    intro x y
    have hz : z (x*y) = A.ρ (β x) (z y) + z x :=
      (mem_cocycles₁_iff _).mp z.2 x y
    change (E.equiv (Multiplicative.ofAdd (z (x*y))) : Q) = _
    rw [hz]
    change (E.equiv (Multiplicative.ofAdd (A.ρ (β x) (z y) + z x)) : Q) = _
    rw [add_comm, originalKernelChart_add]
    have ha := E.conjugate (f₀.1 x) (z y)
    rw [homomorphicLift_above π β f₀ x] at ha
    rw [ha]
    group⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    exact E.equiv.apply_symm_apply (z.1 j)
  right_inv z := by
    apply Subtype.ext
    funext j
    exact congrArg Multiplicative.toAdd (E.equiv.symm_apply_apply (Multiplicative.ofAdd (z j)))

/-- The full same-source lift fibre in the original module chart. -/
def homomorphicLiftModuleCocycleEquiv (π : Q →* B) (β : J →* B)
    (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (f₀ : HomomorphicLift π β) :
    HomomorphicLift π β ≃ cocycles₁ (quotientPullbackRep β A) :=
  (homomorphicLiftEquivCocycle π β f₀).trans
    (originalKernelCocycleEquiv π β A E f₀)

/-- A retained survival predicate is carried exactly, before any
positive enlargement of the restriction image or the lift fibre. -/
def homomorphicLiftModuleRestrictedEquiv (π : Q →* B) (β : J →* B)
    (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (f₀ : HomomorphicLift π β) (P : HomomorphicLift π β → Prop) :
    {f : HomomorphicLift π β // P f} ≃
      {z : cocycles₁ (quotientPullbackRep β A) //
        P ((homomorphicLiftModuleCocycleEquiv π β A E f₀).symm z)} :=
  (homomorphicLiftModuleCocycleEquiv π β A E f₀).subtypeEquiv (fun f ↦ by
    rw [Equiv.symm_apply_apply])

/-- Exact full lift cardinality, still retaining the restricted
transgression image rather than assuming all kernel maps extend. -/
theorem homomorphicLift_card_eq_restriction_image
    (π : Q →* B) (β : J →* B) (hβ : Function.Surjective β)
    (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (f₀ : HomomorphicLift π β) :
    Nat.card (HomomorphicLift π β) =
      Nat.card (coboundaries₁ A) * Nat.card (H1 A) *
        Nat.card (LinearMap.range (quotientCocycleRestriction β A)) := by
  rw [Nat.card_congr (homomorphicLiftEquivCocycle π β f₀),
    Nat.card_congr (originalKernelCocycleEquiv π β A E f₀),
    cocycles_card_eq_quotient_mul_restriction_range β hβ A,
    cocycles_card_eq_coboundaries_mul_H1]

/-- Inflation--restriction for actual fixed-quotient lifts, including
any later survival or surjectivity requirement. Empty fibres are allowed;
no origin lift or splitting is assumed in the statement. -/
theorem homomorphicLift_survival_card_le [Finite J] [Finite Q]
    (π : Q →* B) (β : J →* B) (hβ : Function.Surjective β)
    (A : Rep k B) [Finite A] (E : OriginalKernelModuleChart π A)
    (P : HomomorphicLift π β → Prop) :
    Nat.card {f : HomomorphicLift π β // P f} ≤
      Nat.card A * Nat.card (H1 A) * Nat.card (EquivariantKernelHom β A) := by
  classical
  by_cases h : Nonempty (HomomorphicLift π β)
  · obtain ⟨f₀⟩ := h
    calc
      Nat.card {f : HomomorphicLift π β // P f} ≤ Nat.card (HomomorphicLift π β) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = Nat.card (cocycles₁ (quotientPullbackRep β A)) :=
        Nat.card_congr ((homomorphicLiftEquivCocycle π β f₀).trans
          (originalKernelCocycleEquiv π β A E f₀))
      _ ≤ _ := cocycles_card_le_inflation_restriction β hβ A
  · haveI : IsEmpty (HomomorphicLift π β) := not_nonempty_iff.mp h
    simp

end SymmetricSubgroupAsymptotics
