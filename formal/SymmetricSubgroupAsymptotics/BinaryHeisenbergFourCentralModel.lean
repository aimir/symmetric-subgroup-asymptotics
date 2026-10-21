import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalCarrySpaces
import SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
import SymmetricSubgroupAsymptotics.FiniteGeneratedKernelTable
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantMasks
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! The actual K14 zero-offset extension has a four-element central
commutator carrier. Its coordinates use only the eight kernel vectors and
the already checked thirty-two original top rows. No multiplication table
or list of normal subgroups of the extension is constructed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralModel

abbrev H := BinaryHeisenbergEightNaturalHeads.H
abbrev W := (BinaryHeisenbergEightNaturalHeads.states 14).toSubmodule

def kernelChart : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] W :=
  (BinaryHeisenbergEightNaturalHeads.charts 14).2.equiv

def action : H →* (W ≃ₗ[ZMod 2] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
    (BinaryHeisenbergEightNaturalHeads.states 14).toRepresentation.asGroupHom

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model action
abbrev KernelIndex := Fin 3 → ZMod 2
abbrev GeneratorIndex := KernelIndex ⊕ Fin 5

def generators : GeneratorIndex → Model
  | .inl a => SemidirectProduct.inl (Multiplicative.ofAdd (kernelChart a))
  | .inr j => SemidirectProduct.inr (BinaryHeisenbergEightNaturalHeads.generators j)

theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ := by
  let C := Subgroup.closure (Set.range generators)
  have hk (v : W) : SemidirectProduct.inl (Multiplicative.ofAdd v) ∈ C := by
    have h : generators (Sum.inl (kernelChart.symm v)) ∈ C := Subgroup.subset_closure
      (Set.mem_range_self (Sum.inl (kernelChart.symm v) : GeneratorIndex))
    simpa only [generators, kernelChart.apply_symm_apply] using h
  have ht : (⊤ : Subgroup H) ≤
      C.comap (SemidirectProduct.inr : H →* Model) := by
    rw [← BinaryHeisenbergEightNaturalHeads.generators_full]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self (Sum.inr j : GeneratorIndex))
  apply top_unique
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact C.mul_mem (hk g.left.toAdd) (ht (Subgroup.mem_top g.right))

def row (a : KernelIndex × Fin 32) : Model :=
  ⟨Multiplicative.ofAdd (kernelChart a.1), BinaryEightOriginalRowActions.heisenbergRow a.2⟩

theorem row_bijective : Function.Bijective row := by
  constructor
  · intro a b h
    have hl := congrArg (fun g : Model => g.left.toAdd) h
    have hr := congrArg (fun g : Model => g.right) h
    exact Prod.ext (kernelChart.injective hl)
      (BinaryEightOriginalRowActions.heisenbergRow_bijective.1 hr)
  · intro g
    obtain ⟨i, hi⟩ := BinaryEightOriginalRowActions.heisenbergRow_bijective.2 g.right
    refine ⟨(kernelChart.symm g.left.toAdd, i), ?_⟩
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd (kernelChart.apply_symm_apply g.left.toAdd)
    · exact hi

def rowEquiv : (KernelIndex × Fin 32) ≃ Model := Equiv.ofBijective row row_bijective

theorem card_model : Nat.card Model = 256 := by
  rw [← Nat.card_congr rowEquiv]
  simp [KernelIndex, Nat.card_eq_fintype_card]

def constantVector (a : ZMod 2) : W :=
  ⟨fun _ => a, by
    change (fun _ : Fin 8 => a) ∈ (BinaryHeisenbergEightNaturalHeads.charts 14).2.space
    fin_cases a <;> decide +kernel⟩

def centralRow (a : Fin 2 → ZMod 2) : Model :=
  ⟨Multiplicative.ofAdd (constantVector (a 0)),
    BinaryHeisenbergEightNaturalHeads.generators 0 ^ (a 1).val⟩

/-- Finite checks compare the literal coordinates; group equality itself
can contain noncomputable subtype decision transports. -/
def CoordinateEq (g h : Model) : Prop :=
  (∀ x : Fin 8, g.left.toAdd.val x = h.left.toAdd.val x) ∧
  (∀ x : Fin 8, g.right.val x = h.right.val x)

instance (g h : Model) : Decidable (CoordinateEq g h) :=
  inferInstanceAs (Decidable
    ((∀ x : Fin 8, g.left.toAdd.val x = h.left.toAdd.val x) ∧
      (∀ x : Fin 8, g.right.val x = h.right.val x)))

private theorem eq_of_coordinateEq {g h : Model} (he : CoordinateEq g h) : g = h := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact Subtype.ext (funext he.1)
  · exact Subtype.ext (Equiv.ext he.2)

private theorem centralRow_injective : Function.Injective centralRow := by
  have hc : ∀ a b : Fin 2 → ZMod 2, CoordinateEq (centralRow a) (centralRow b) →
      ∀ j, a j = b j := by decide +kernel
  intro a b he
  apply funext
  apply hc a b
  exact ⟨fun x => congrArg (fun g : Model => g.left.toAdd.val x) he,
    fun x => congrArg (fun g : Model => g.right.val x) he⟩

def centralTable : FiniteGeneratedKernelTable
    (I := Fin 2 → ZMod 2) generators where
  element := centralRow
  element_injective := centralRow_injective
  identity := 0
  identity_eq := eq_of_coordinateEq (by decide +kernel)
  multiply a b := a + b
  multiply_eq := by
    have hc : ∀ a b : Fin 2 → ZMod 2,
        CoordinateEq (centralRow (a + b)) (centralRow a * centralRow b) := by decide +kernel
    exact fun a b => eq_of_coordinateEq (hc a b)
  inverse a := a
  inverse_eq := by
    have hc : ∀ a : Fin 2 → ZMod 2,
        CoordinateEq (centralRow a) (centralRow a)⁻¹ := by decide +kernel
    exact fun a => eq_of_coordinateEq (hc a)
  conjugate _ := Equiv.refl _
  conjugate_eq := by
    have hc : ∀ (j : GeneratorIndex) (a : Fin 2 → ZMod 2),
        CoordinateEq (centralRow a) (generators j * centralRow a * (generators j)⁻¹) := by
      decide +kernel
    exact fun j a => eq_of_coordinateEq (hc j a)

abbrev D := centralTable.subgroup

instance : D.Normal := centralTable.normal generators_full

theorem card_D : Nat.card D = 4 := by
  rw [← Nat.card_congr centralTable.chartEquiv]
  simp [Nat.card_eq_fintype_card]

private theorem generator_commutators : ∀ i j : GeneratorIndex,
    ∃ a : Fin 2 → ZMod 2, centralRow a = ⁅generators i, generators j⁆ := by
  have hc : ∀ i j : GeneratorIndex, ∃ a : Fin 2 → ZMod 2,
      CoordinateEq (centralRow a) ⁅generators i, generators j⁆ := by decide +kernel
  intro i j
  obtain ⟨a, ha⟩ := hc i j
  exact ⟨a, eq_of_coordinateEq ha⟩

theorem commutator_le_D : commutator Model ≤ D := by
  apply commutator_le_of_generator_commutators D generators generators_full
  intro i j
  exact generator_commutators i j

theorem commutator_card_le_four : Nat.card (commutator Model) ≤ 4 :=
  (Subgroup.card_le_of_le commutator_le_D).trans_eq card_D

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFourCentralModel
