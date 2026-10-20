import SymmetricSubgroupAsymptotics.FiniteIsotypicGeneratorSharing

/-! Homogeneous row data with actual row equivalences, and the generator
bound for all rows of small multiplicity. The threshold is integral and
will later be chosen of square-root size. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

structure FiniteIsotypicRowData
    (R M : Type) [Ring R] [AddCommGroup M] [Module R M] where
  multiplicity : isotypicComponents R M → ℕ
  simplePart : isotypicComponents R M → Submodule R M
  positive : ∀ i, 0<multiplicity i
  simple : ∀ i, IsSimpleModule R (simplePart i)
  simple_le : ∀ i, simplePart i ≤ (i : Submodule R M)
  rowEquiv : ∀ i, i.val ≃ₗ[R] (Fin (multiplicity i) → simplePart i)

theorem finite_isotypic_rowData_nonempty
    (R M : Type) [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] : Nonempty (FiniteIsotypicRowData R M) := by
  let I := isotypicComponents R M
  letI (i : I) : Module.Finite R i.val := Module.Finite.of_finite
  have hrow (i : I) : ∃ (n : ℕ) (_ : NeZero n) (S : Submodule R M),
      S ≤ (i : Submodule R M) ∧ IsSimpleModule R S ∧
        Nonempty (i.val ≃ₗ[R] Fin n → S) :=
    (IsIsotypic.isotypicComponents i.property).submodule_linearEquiv_fun
  choose d hd S hle hs e using hrow
  exact ⟨{ multiplicity := d
           simplePart := S
           positive := fun i => Nat.pos_of_ne_zero (hd i).out
           simple := hs
           simple_le := hle
           rowEquiv := fun i => (e i).some }⟩

theorem moduleGeneratedBy_simple_power_of_le
    {R S : Type} [Ring R] [AddCommGroup S] [Module R S]
    [Finite S] [IsSimpleModule R S] (m t : ℕ) (hmt : m≤t) :
    ModuleGeneratedBy R (Fin m → S) t := by
  letI : Nontrivial S := IsSimpleModule.nontrivial R S
  letI : Module.Finite (Module.End R S) S := Module.Finite.of_finite
  have hp : 0<Module.finrank (Module.End R S) S := Module.finrank_pos
  apply schurPi_moduleGeneratedBy m t
  nlinarith

namespace FiniteIsotypicRowData

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] (D : FiniteIsotypicRowData R M)

def lowIndex (t : ℕ) := {i : isotypicComponents R M // D.multiplicity i≤t}

instance lowIndex_finite (t : ℕ) [Finite (isotypicComponents R M)] :
    Finite (D.lowIndex t) := by
  unfold lowIndex
  infer_instance

def lowModule (t : ℕ) : Submodule R M := ⨆ i : D.lowIndex t, i.val.val

omit [IsSemisimpleModule R M] in
theorem row_generated (i : isotypicComponents R M) (t : ℕ)
    (hi : D.multiplicity i≤t) : ModuleGeneratedBy R i.val t := by
  letI : IsSimpleModule R (D.simplePart i) := D.simple i
  exact ModuleGeneratedBy.congr (D.rowEquiv i).symm
    (moduleGeneratedBy_simple_power_of_le (D.multiplicity i) t hi)

theorem lowModule_generated (t : ℕ) : ModuleGeneratedBy R (D.lowModule t) t := by
  letI : Module.Finite R M := Module.Finite.of_finite
  letI : Fintype (isotypicComponents R M) := Fintype.ofFinite _
  letI : Fintype (D.lowIndex t) := Fintype.ofFinite _
  exact moduleGeneratedBy_isotypic_selection
    (fun i : D.lowIndex t => i.val) Subtype.val_injective t
    (fun i => D.row_generated i.val t i.property)

end FiniteIsotypicRowData
end SymmetricSubgroupAsymptotics
