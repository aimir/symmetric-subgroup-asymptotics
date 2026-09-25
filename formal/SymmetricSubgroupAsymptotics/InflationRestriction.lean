import SymmetricSubgroupAsymptotics.CocycleCardinality

/-!
# Same-source restriction and inflation of actual cocycles

Restriction is taken on the literal kernel of the original quotient map.
The equivariance condition retains conjugation by the entire source.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open groupCohomology

universe u
variable {k J B : Type u} [CommRing k] [Group J] [Group B]

abbrev quotientPullbackRep (β : J →* B) (A : Rep k B) : Rep k J :=
  Rep.of (A.ρ.comp β)

/-- The literal conjugation of an element of the original kernel. -/
def quotientKernelConjugate (β : J →* B) (j : J) (x : β.ker) : β.ker :=
  ⟨j * x * j⁻¹, by
    change β (j * x * j⁻¹) = 1
    simp [show β (x : J) = 1 from x.property]⟩

/-- Actual additive homomorphisms on the original kernel, equivariant
for the actual source action. No quotient action on the source kernel
or independence of retained columns is postulated. -/
def EquivariantKernelHom (β : J →* B) (A : Rep k B) :=
  {f : Additive β.ker →+ A // ∀ j x,
    f (Additive.ofMul (quotientKernelConjugate β j x)) =
      A.ρ (β j) (f (Additive.ofMul x))}

/-- Inflation along the fixed original quotient map. -/
def quotientCocycleInflation (β : J →* B) (A : Rep k B) :
    cocycles₁ A →ₗ[k] cocycles₁ (quotientPullbackRep β A) where
  toFun z := ⟨fun j ↦ z (β j), (mem_cocycles₁_iff _).mpr (fun x y ↦ by
    simpa using (mem_cocycles₁_iff _).mp z.2 (β x) (β y))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of the actual cocycle function to the literal kernel. -/
def quotientCocycleRestriction (β : J →* B) (A : Rep k B) :
    cocycles₁ (quotientPullbackRep β A) →ₗ[k] (β.ker → A) where
  toFun z x := z x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quotientCocycle_constant_on_fibres (β : J →* B) (A : Rep k B)
    (z : LinearMap.ker (quotientCocycleRestriction β A))
    {x y : J} (h : β x = β y) : z.1 x = z.1 y := by
  have hz : z.1 (y⁻¹ * x) = 0 := by
    exact congrFun z.2 (⟨y⁻¹ * x, by simp [MonoidHom.mem_ker, h]⟩ : β.ker)
  have he := (mem_cocycles₁_iff _).mp z.1.2 y (y⁻¹ * x)
  simpa [hz] using he

/-- Descent of precisely those cocycles which vanish on the original
kernel; surjectivity is the only property of the quotient map used. -/
def quotientCocycleDescent (β : J →* B) (hβ : Function.Surjective β)
    (A : Rep k B) (z : LinearMap.ker (quotientCocycleRestriction β A)) :
    cocycles₁ A := by
  let s : B → J := fun b ↦ (hβ b).choose
  have hs (b : B) : β (s b) = b := (hβ b).choose_spec
  refine ⟨fun b ↦ z.1 (s b), (mem_cocycles₁_iff _).mpr ?_⟩
  intro b c
  have he := (mem_cocycles₁_iff _).mp z.1.2 (s b) (s c)
  have hf := quotientCocycle_constant_on_fibres β A z
    (x := s (b*c)) (y := s b * s c) (by simp [hs])
  simpa [hs] using hf.trans he

@[simp] theorem quotientCocycleDescent_apply (β : J →* B)
    (hβ : Function.Surjective β) (A : Rep k B)
    (z : LinearMap.ker (quotientCocycleRestriction β A)) (j : J) :
    quotientCocycleDescent β hβ A z (β j) = z.1 j := by
  exact quotientCocycle_constant_on_fibres β A z (hβ (β j)).choose_spec

/-- The restriction kernel is exactly the inflated cocycles of the
original quotient, as an equivalence of actual objects. -/
def quotientCocycleRestrictionKernelEquiv (β : J →* B)
    (hβ : Function.Surjective β) (A : Rep k B) :
    LinearMap.ker (quotientCocycleRestriction β A) ≃ cocycles₁ A where
  toFun := quotientCocycleDescent β hβ A
  invFun z := ⟨quotientCocycleInflation β A z, by
    ext x
    change z (β x) = 0
    rw [show β (x : J) = 1 from x.property, cocycles₁_map_one]⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    exact quotientCocycleDescent_apply β hβ A z j
  right_inv z := by
    apply Subtype.ext
    funext b
    obtain ⟨j, rfl⟩ := hβ b
    exact quotientCocycleDescent_apply β hβ A _ j

/-- Restriction really is an equivariant homomorphism, even when the
original source kernel is nonabelian. -/
def quotientCocycleKernelHom (β : J →* B) (A : Rep k B)
    (z : cocycles₁ (quotientPullbackRep β A)) : EquivariantKernelHom β A := by
  refine ⟨{ toFun := fun x ↦ z x.toMul
            map_zero' := cocycles₁_map_one z
            map_add' := ?_ }, ?_⟩
  · intro x y
    change z ((x.toMul : J) * (y.toMul : J)) = _
    have he := (mem_cocycles₁_iff _).mp z.2 (x.toMul : J) (y.toMul : J)
    simpa [quotientPullbackRep, show β (x.toMul : J) = 1 from x.toMul.property,
      add_comm] using he
  · intro j x
    change z (j * x * j⁻¹) = A.ρ (β j) (z x)
    have hz (a b : J) : z (a*b) = A.ρ (β a) (z b) + z a :=
      (mem_cocycles₁_iff _).mp z.2 a b
    rw [hz, hz]
    simp only [map_mul, show β (x : J) = 1 from x.property, mul_one]
    have hi := cocycles₁_map_inv z j
    change A.ρ (β j) (z j⁻¹) = -z j at hi
    rw [hi]
    abel

instance equivariantKernelHom_finite [Finite J] (β : J →* B)
    (A : Rep k B) [Finite A] : Finite (EquivariantKernelHom β A) := by
  apply Finite.of_injective (fun f : EquivariantKernelHom β A ↦
    (f.1 : Additive β.ker → A))
  intro f g h
  exact Subtype.ext (DFunLike.coe_injective h)

/-- The image of restriction embeds in the entire equivariant Hom
space. The latter may contain maps obstructed by transgression. -/
def quotientRestrictionRangeHom (β : J →* B) (A : Rep k B)
    (y : LinearMap.range (quotientCocycleRestriction β A)) :
    EquivariantKernelHom β A :=
  quotientCocycleKernelHom β A (Classical.choose y.property)

theorem quotientRestrictionRangeHom_apply (β : J →* B) (A : Rep k B)
    (y : LinearMap.range (quotientCocycleRestriction β A)) (x : β.ker) :
    (quotientRestrictionRangeHom β A y).1 (Additive.ofMul x) = y.1 x :=
  congrFun (Classical.choose_spec y.property) x

theorem quotientRestrictionRangeHom_injective (β : J →* B) (A : Rep k B) :
    Function.Injective (quotientRestrictionRangeHom β A) := by
  intro y z h
  apply Subtype.ext
  funext x
  have he := congrArg (fun f : EquivariantKernelHom β A ↦
    f.1 (Additive.ofMul x)) h
  simpa only [quotientRestrictionRangeHom_apply] using he

/-- Exact cardinality retains the actual restriction image, and hence
every obstruction to extending a kernel homomorphism. -/
theorem cocycles_card_eq_quotient_mul_restriction_range
    (β : J →* B) (hβ : Function.Surjective β) (A : Rep k B) :
    Nat.card (cocycles₁ (quotientPullbackRep β A)) =
      Nat.card (cocycles₁ A) *
        Nat.card (LinearMap.range (quotientCocycleRestriction β A)) := by
  rw [Submodule.card_eq_card_quotient_mul_card
    (LinearMap.ker (quotientCocycleRestriction β A))]
  rw [Nat.card_congr (quotientCocycleRestrictionKernelEquiv β hβ A)]
  rw [Nat.card_congr (quotientCocycleRestriction β A).quotKerEquivRange.toEquiv]

/-- The cohomological inflation--restriction bound on the original
source. It neither asserts that all kernel maps extend nor divides out
the coboundary factor. -/
theorem cocycles_card_le_inflation_restriction [Finite J]
    (β : J →* B) (hβ : Function.Surjective β) (A : Rep k B) [Finite A] :
    Nat.card (cocycles₁ (quotientPullbackRep β A)) ≤
      Nat.card A * Nat.card (H1 A) * Nat.card (EquivariantKernelHom β A) := by
  rw [cocycles_card_eq_quotient_mul_restriction_range β hβ A]
  exact Nat.mul_le_mul (cocycles_card_le_module_mul_H1 A)
    (Nat.card_le_card_of_injective _ (quotientRestrictionRangeHom_injective β A))

end SymmetricSubgroupAsymptotics
