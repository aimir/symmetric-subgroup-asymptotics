import SymmetricSubgroupAsymptotics.Non2LiftBound

/-!
# The actual Sylow source in the non-2 lift reduction

The normalizer is taken in the original source. Its map onto the original
quotient is proved by Frattini's argument. Restriction to a Sylow subgroup
detects homomorphisms into abelian p-groups, without assuming that the
source kernel or its proper subdirect cores are abelian.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

universe u
variable {J B : Type u} {F A : Type*} [Group J] [Group B] [Group F] [CommGroup A]

/-- The actual normalizer supplement to the original quotient kernel. -/
def quotientSylowNormalizer {p : ℕ} (β : J →* B) (P : Sylow p β.ker) : Subgroup J :=
  Subgroup.normalizer (P.map β.ker.subtype)

/-- The Sylow normalizer maps onto the same original quotient. Its
action on the Sylow subgroup is not replaced by an assumed B-action. -/
theorem quotientSylowNormalizer_surjective [Finite J] {p : ℕ} [Fact p.Prime]
    (β : J →* B) (hβ : Function.Surjective β) (P : Sylow p β.ker) :
    Function.Surjective (β.comp (quotientSylowNormalizer β P).subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [(Subgroup.map_eq_range_iff).mpr
    (show Codisjoint (quotientSylowNormalizer β P) β.ker from
      codisjoint_iff.mpr (Sylow.normalizer_sup_eq_top P))]
  exact MonoidHom.range_eq_top.mpr hβ

/-- A Sylow subgroup maps onto every p-group homomorphic image. -/
theorem sylow_image_eq_range [Finite F] {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (P : Sylow p F) (f : F →* A) :
    (P : Subgroup F).map f = f.range := by
  let P' := P.mapSurjective f.rangeRestrict_surjective
  have hp' : (P' : Subgroup f.range) = ⊤ :=
    (P'.is_maximal' ((hA.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  have hm := congrArg (Subgroup.map f.range.subtype) hp'
  change ((P : Subgroup F).map f.rangeRestrict).map f.range.subtype = _ at hm
  rw [Subgroup.map_map, show f.range.subtype.comp f.rangeRestrict = f from rfl] at hm
  simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using hm

/-- Actual restriction on homomorphisms into an abelian p-group is
injective, including for a nonabelian original kernel. -/
theorem sylow_hom_restriction_injective [Finite F] {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (P : Sylow p F) :
    Function.Injective (fun f : F →* A ↦ f.comp (P : Subgroup F).subtype) := by
  intro f g h
  let d : F →* A := f / g
  have hp : (P : Subgroup F).map d = ⊥ := by
    apply le_antisymm
    · rintro a ⟨x, hx, rfl⟩
      change f x / g x = 1
      exact div_eq_one.mpr (DFunLike.congr_fun h ⟨x, hx⟩)
    · exact bot_le
  have hr : d.range = ⊥ := (sylow_image_eq_range hA P d).symm.trans hp
  apply MonoidHom.ext
  intro x
  have hx : d x ∈ d.range := ⟨x, rfl⟩
  rw [hr] at hx
  exact div_eq_one.mp hx

/-- Literal conjugation by the original Sylow normalizer. -/
def quotientSylowConjugate {p : ℕ} (β : J →* B) (P : Sylow p β.ker)
    (j : quotientSylowNormalizer β P) (x : (P : Subgroup β.ker)) :
    (P : Subgroup β.ker) :=
  ⟨quotientKernelConjugate β (j : J) (x : β.ker), by
    have hx : ((x : β.ker) : J) ∈ P.map β.ker.subtype := ⟨x, x.property, rfl⟩
    have hy := (Subgroup.mem_normalizer_iff.mp j.property ((x : β.ker) : J)).mp hx
    obtain ⟨y, hy, he⟩ := hy
    have he' : y = quotientKernelConjugate β (j : J) (x : β.ker) := Subtype.ext he
    exact he' ▸ hy⟩

section ModuleRestriction
variable {k : Type u} [CommRing k] (β : J →* B) {p : ℕ}
    (P : Sylow p β.ker) (M : Rep k B)

/-- The actual equivariant Hom space on the chosen Sylow subgroup.
The acting group is its original normalizer, not a fabricated quotient
action on the source. -/
def SylowEquivariantKernelHom :=
  {f : Additive (P : Subgroup β.ker) →+ M // ∀ j x,
    f (Additive.ofMul (quotientSylowConjugate β P j x)) =
      M.ρ (β (j : J)) (f (Additive.ofMul x))}

/-- Restriction retains every normalizer-equivariance equation. -/
def equivariantKernelHomSylowRestriction :
    EquivariantKernelHom β M → SylowEquivariantKernelHom β P M := fun f ↦
  ⟨{ toFun := fun x ↦ f.1 (Additive.ofMul (x.toMul : β.ker))
     map_zero' := f.1.map_zero
     map_add' := fun x y ↦ f.1.map_add
       (Additive.ofMul (x.toMul : β.ker)) (Additive.ofMul (y.toMul : β.ker)) },
    fun j x ↦ f.2 (j : J) (x : β.ker)⟩

theorem equivariantKernelHomSylowRestriction_injective [Finite J] [Fact p.Prime]
    (hM : IsPGroup p (Multiplicative M)) :
    Function.Injective (equivariantKernelHomSylowRestriction β P M) := by
  intro f g h
  apply Subtype.ext
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply sylow_hom_restriction_injective hM P
  ext x
  have he := congrArg (fun t : SylowEquivariantKernelHom β P M ↦
    t.1 (Additive.ofMul x)) h
  exact congrArg Multiplicative.ofAdd he

instance sylowEquivariantKernelHom_finite [Finite J] [Finite M] :
    Finite (SylowEquivariantKernelHom β P M) := by
  apply Finite.of_injective (fun f : SylowEquivariantKernelHom β P M ↦
    (f.1 : Additive (P : Subgroup β.ker) → M))
  intro f g h
  exact Subtype.ext (DFunLike.coe_injective h)

/-- This numerical reduction still retains all equations for the
actual normalizer action on the actual Sylow subgroup. -/
theorem equivariantKernelHom_card_le_Sylow [Finite J] [Finite M] [Fact p.Prime]
    (hM : IsPGroup p (Multiplicative M)) :
    Nat.card (EquivariantKernelHom β M) ≤ Nat.card (SylowEquivariantKernelHom β P M) :=
  Nat.card_le_card_of_injective _ (equivariantKernelHomSylowRestriction_injective β P M hM)

end ModuleRestriction

/-- The first two structural reductions of the non-2 lift bound,
applied to actual survival-restricted lifts in the original extension. -/
theorem homomorphicLift_survival_card_le_Sylow
    {k Q : Type u} [CommRing k] [Group Q] [Finite J] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (π : Q →* B) (β : J →* B) (hβ : Function.Surjective β)
    (M : Rep k B) [Finite M] (E : OriginalKernelModuleChart π M)
    (hM : IsPGroup p (Multiplicative M)) (P : Sylow p β.ker)
    (S : HomomorphicLift π β → Prop) :
    Nat.card {f : HomomorphicLift π β // S f} ≤
      Nat.card M * Nat.card (groupCohomology.H1 M) *
        Nat.card (SylowEquivariantKernelHom β P M) :=
  (homomorphicLift_survival_card_le π β hβ M E S).trans
    (Nat.mul_le_mul_left _ (equivariantKernelHom_card_le_Sylow β P M hM))

end SymmetricSubgroupAsymptotics
