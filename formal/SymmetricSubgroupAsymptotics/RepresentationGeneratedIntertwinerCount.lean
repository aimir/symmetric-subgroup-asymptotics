import SymmetricSubgroupAsymptotics.ModuleSubquotientGeneratorBound
import SymmetricSubgroupAsymptotics.TraceyPrimePowerInput

/-! Literal evaluation on generating vectors counts equivariant maps.
The hypothesis is generation of the actual source module, rather than
an assumed numerical bound on its space of maps. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

namespace ModuleGeneratedBy

variable {R M N : Type} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Every linear map is determined by its values on the supplied generators. -/
theorem linearMap_card_le [Finite N] {H : ℕ}
    (hgen : ModuleGeneratedBy R M H) :
    Nat.card (M →ₗ[R] N) ≤ Nat.card N ^ H := by
  obtain ⟨v, hv⟩ := hgen
  let evaluation : (M →ₗ[R] N) → (Fin H → N) := fun f i => f (v i)
  have hinj : Function.Injective evaluation := by
    intro f g h
    apply (Submodule.linearMap_eq_iff_of_span_eq_top f g hv).mpr
    rintro ⟨x, i, rfl⟩
    exact congrFun h i
  have h := Nat.card_le_card_of_injective evaluation hinj
  simpa only [Nat.card_fun, Nat.card_fin] using h

end ModuleGeneratedBy

variable {k G V W : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A finitely generated source and a finite target give finitely many intertwiners. -/
theorem representationGenerated_intertwiner_finite [Finite W]
    (rho : Representation k G V) (sigma : Representation k G W)
    {H : ℕ} (hgen : RepresentationGeneratedBy rho H) :
    Finite (rho.IntertwiningMap sigma) := by
  obtain ⟨v, hv⟩ := hgen
  let e := Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
  let evaluation : rho.IntertwiningMap sigma → (Fin H → W) :=
    fun f i => sigma.asModuleEquiv (e f (v i))
  apply Finite.of_injective evaluation
  intro f g h
  apply e.injective
  apply (Submodule.linearMap_eq_iff_of_span_eq_top (e f) (e g) hv).mpr
  rintro ⟨x, i, rfl⟩
  exact sigma.asModuleEquiv.injective (congrFun h i)

/-- H actual representation generators bound the complete intertwiner set. -/
theorem representationGenerated_intertwiner_card_le [Finite W]
    (rho : Representation k G V) (sigma : Representation k G W)
    {H : ℕ} (hgen : RepresentationGeneratedBy rho H) :
    Nat.card (rho.IntertwiningMap sigma) ≤ Nat.card W ^ H := by
  obtain ⟨v, hv⟩ := hgen
  let e := Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
  let evaluation : rho.IntertwiningMap sigma → (Fin H → W) :=
    fun f i => sigma.asModuleEquiv (e f (v i))
  have hi : Function.Injective evaluation := by
    intro f g h
    apply e.injective
    apply (Submodule.linearMap_eq_iff_of_span_eq_top (e f) (e g) hv).mpr
    rintro ⟨x, i, rfl⟩
    exact sigma.asModuleEquiv.injective (congrFun h i)
  have h := Nat.card_le_card_of_injective evaluation hi
  simpa only [Nat.card_fun, Nat.card_fin] using h

end SymmetricSubgroupAsymptotics
