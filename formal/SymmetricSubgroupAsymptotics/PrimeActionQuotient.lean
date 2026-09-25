import SymmetricSubgroupAsymptotics.PrimeAbelianization
import SymmetricSubgroupAsymptotics.Non2SylowReduction

/-! Actual automorphism and Sylow-normalizer actions on the prime quotient. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {D G : Type*} [Group D] [Group G] [Finite G]

/-- Functorial descent of the given action, without forcing it to factor
through any smaller acting group. -/
def primeAbelianizationRepresentation (ρ : D →* MulAut G) :
    Representation (ZMod p) D (PrimeAbelianization p G) where
  toFun d := primeAbelianizationMapHom p (ρ d).toMonoidHom
  map_one' := by
    change primeAbelianizationMapHom p (ρ 1).toMonoidHom = LinearMap.id
    rw [map_one]
    exact primeAbelianizationMapHom_id p
  map_mul' x y := by
    rw [map_mul]
    exact primeAbelianizationMapHom_comp p (ρ y).toMonoidHom (ρ x).toMonoidHom

@[simp] theorem primeAbelianizationRepresentation_eval (ρ : D →* MulAut G) (d : D) (x : G) :
    primeAbelianizationRepresentation p ρ d
      (primeAbelianizationMap p G (Additive.ofMul x)) =
        primeAbelianizationMap p G (Additive.ofMul (ρ d x)) :=
  primeAbelianizationMapHom_apply p (ρ d).toMonoidHom x

/-- Equivariance before descent is equivalent to equivariance on the
actual elementary quotient, with every equation retained. -/
theorem primeAbelianizationLift_equivariant_iff
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : D →* MulAut G) (σ : Representation (ZMod p) D V) (f : Additive G →+ V) :
    (∀ d x, f (Additive.ofMul (ρ d x)) = σ d (f (Additive.ofMul x))) ↔
      ∀ d w, primeAbelianizationLift p G f (primeAbelianizationRepresentation p ρ d w) =
        σ d (primeAbelianizationLift p G f w) := by
  constructor
  · intro h d w
    obtain ⟨x,rfl⟩ := primeAbelianizationMap_surjective p G w
    change primeAbelianizationLift p G f
      (primeAbelianizationRepresentation p ρ d
        (primeAbelianizationMap p G (Additive.ofMul x.toMul))) = _
    rw [primeAbelianizationRepresentation_eval,primeAbelianizationLift_apply,
      primeAbelianizationLift_apply]
    exact h d x.toMul
  · intro h d x
    have hx := h d (primeAbelianizationMap p G (Additive.ofMul x))
    simpa only [primeAbelianizationRepresentation_eval,primeAbelianizationLift_apply] using hx

/-- Equivariant group homomorphisms are exactly intertwining maps on the
actual prime quotient. This is an equivalence of complete literal fibres. -/
def primeEquivariantHomEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : D →* MulAut G) (σ : Representation (ZMod p) D V) :
    {f : Additive G →+ V // ∀ d x,
      f (Additive.ofMul (ρ d x)) = σ d (f (Additive.ofMul x))} ≃
        Representation.IntertwiningMap (primeAbelianizationRepresentation p ρ) σ where
  toFun f := (primeAbelianizationLift p G f.1).intertwiningMap_of_isIntertwiningMap
    _ _ ((primeAbelianizationLift_equivariant_iff p ρ σ f.1).mp f.2)
  invFun f := ⟨f.toLinearMap.toAddMonoidHom.comp (primeAbelianizationMap p G),by
    intro d x
    have h := LinearMap.congr_fun (f.isIntertwining' d)
      (primeAbelianizationMap p G (Additive.ofMul x))
    simpa only [AddMonoidHom.comp_apply,LinearMap.toAddMonoidHom_coe,LinearMap.comp_apply,
      primeAbelianizationRepresentation_eval] using h⟩
  left_inv f := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    exact primeAbelianizationLift_apply p G f.1 x
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    obtain ⟨x,rfl⟩ := primeAbelianizationMap_surjective p G w
    exact primeAbelianizationLift_apply p G _ x

section Sylow

variable {J B : Type} [Group J] [Group B]

/-- The original normalizer acts on the actual Sylow subgroup by
conjugation. Its domain is not replaced by the quotient B. -/
def quotientSylowConjugation (β : J →* B) (P : Sylow p β.ker) :
    quotientSylowNormalizer β P →* MulAut (P : Subgroup β.ker) where
  toFun j :=
    { toFun := quotientSylowConjugate β P j
      invFun := quotientSylowConjugate β P j⁻¹
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change (j : J)⁻¹ * ((j : J) * (x : β.ker) * (j : J)⁻¹) * ((j : J)⁻¹)⁻¹ = (x : β.ker)
        simp [mul_assoc]
      right_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change (j : J) * ((j : J)⁻¹ * (x : β.ker) * ((j : J)⁻¹)⁻¹) * (j : J)⁻¹ = (x : β.ker)
        simp [mul_assoc]
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        change (j : J) * ((x : β.ker) * (y : β.ker)) * (j : J)⁻¹ =
          ((j : J) * (x : β.ker) * (j : J)⁻¹) * ((j : J) * (y : β.ker) * (j : J)⁻¹)
        simp [mul_assoc] }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change (1 : J) * (x : β.ker) * (1 : J)⁻¹ = (x : β.ker)
    simp
  map_mul' j k := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((j : J) * (k : J)) * (x : β.ker) * ((j : J) * (k : J))⁻¹ =
      (j : J) * ((k : J) * (x : β.ker) * (k : J)⁻¹) * (j : J)⁻¹
    simp [mul_assoc]

omit [Fact p.Prime] in
@[simp] theorem quotientSylowConjugation_apply (β : J →* B) (P : Sylow p β.ker)
    (j : quotientSylowNormalizer β P) (x : (P : Subgroup β.ker)) :
    quotientSylowConjugation p β P j x = quotientSylowConjugate β P j x := rfl

/-- The complete actual Sylow-normalizer Hom fibre descends reversibly.
The source retains its D-action; only the target is inflated from B. -/
def sylowEquivariantPrimeHomEquiv [Finite J]
    (β : J →* B) (P : Sylow p β.ker) (M : Rep (ZMod p) B) [Finite M] :
    SylowEquivariantKernelHom β P M ≃
      Representation.IntertwiningMap
        (primeAbelianizationRepresentation p (quotientSylowConjugation p β P))
        (M.ρ.comp (β.comp (quotientSylowNormalizer β P).subtype)) :=
  primeEquivariantHomEquiv p (quotientSylowConjugation p β P)
    (M.ρ.comp (β.comp (quotientSylowNormalizer β P).subtype))

end Sylow

end SymmetricSubgroupAsymptotics
