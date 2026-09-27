import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads
import SymmetricSubgroupAsymptotics.RepresentationElementHead
import SymmetricSubgroupAsymptotics.RepresentationQuotientElementHead
import SymmetricSubgroupAsymptotics.TernarySignResolution

/-!
# Nontrivial binary signs kill ternary invariant heads

A scalar action through a nontrivial binary character has no fixed vectors
over `F₃`.  This remains true for every actual subrepresentation.  Combining
that observation with jointly injective equivariant coordinates proves the
zero-head statement used by the degree-27 inversion-image fork: no splitting
or coordinate independence is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

open OddMarkerTernaryChart TernarySignCocycles TernarySignResolution

variable {B A : Type} [Group B] [AddCommGroup A] [Module (ZMod 3) A]

/-- The scalar sign action on an arbitrary ternary module.  The trivial
`Rep` supplies only the underlying module to the already checked scalar
construction. -/
abbrev ternarySignRepresentation
    (χ : B →* Multiplicative (ZMod 2)) : Representation (ZMod 3) B A :=
  scalarRepresentation (Rep.trivial (ZMod 3) B A) χ

/-- One actual element with nontrivial sign acts as `-1`, so its fixed
space on the whole original ternary module is zero. -/
theorem signScalarRepresentation_exists_fixedSpace_eq_bot
    (χ : B →* Multiplicative (ZMod 2)) (hχ : χ ≠ 1) :
    ∃ s : B, representationElementFixedSpace
      (@ternarySignRepresentation B A _ _ _ χ) s = ⊥ := by
  obtain ⟨s, hs⟩ := exists_nontrivial_sign χ hχ
  refine ⟨s, le_antisymm ?_ bot_le⟩
  intro v hv
  rw [mem_representationElementFixedSpace] at hv
  change signScalar (χ s) • (v : A) = v at hv
  rw [hs, signScalar_nontrivial] at hv
  rw [Submodule.mem_bot]
  have hz : ((-1 : ZMod 3) - 1) • (v : A) = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr hv
  simpa only [show (-1 : ZMod 3) - 1 = 1 by decide, one_smul] using hz

/-- Every actual invariant submodule of a nontrivial scalar sign module has
zero ternary relative head.  This is the Maschke consequence needed here,
proved directly from one fixed-space calculation. -/
theorem signScalar_subrepresentation_characterHead_eq_zero
    [FiniteDimensional (ZMod 3) A]
    (χ : B →* Multiplicative (ZMod 2)) (hχ : χ ≠ 1)
    (S : Subrepresentation (@ternarySignRepresentation B A _ _ _ χ)) :
    Module.finrank (ZMod 3)
      (primeActionCharacters (A := B) (G := Multiplicative S.toSubmodule) 3
        (representationGroupAction S.toRepresentation)) = 0 := by
  obtain ⟨s, hs⟩ := signScalarRepresentation_exists_fixedSpace_eq_bot
    (A := A) χ hχ
  have h := subrepresentationCharacterHead_le_ambient_elementFixedSpace
    (@ternarySignRepresentation B A _ _ _ χ) S s
  rw [hs] at h
  have hzero : Module.finrank (ZMod 3)
      (primeActionCharacters (A := B) (G := Multiplicative S.toSubmodule) 3
        (representationGroupAction S.toRepresentation)) ≤ 0 := by
    simpa using h
  exact Nat.eq_zero_of_le_zero hzero

/-- Joint equivariant coordinates carrying actual nontrivial binary signs
force the complete original ternary invariant-character head to vanish.
The coordinate maps need only separate points jointly; their images may be
proper and the source may be a non-split subrepresentation or quotient
already constructed elsewhere. -/
theorem representationCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    {V ι : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Fintype ι]
    (W : ι → Type)
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 3) (W i)]
    [∀ i, FiniteDimensional (ZMod 3) (W i)]
    (ρ : Representation (ZMod 3) B V)
    (χ : ∀ _ : ι, B →* Multiplicative (ZMod 2))
    (hχ : ∀ i, χ i ≠ 1)
    (f : ∀ i, ρ.IntertwiningMap (@ternarySignRepresentation B (W i) _ _ _ (χ i)))
    (hf : Function.Injective (fun v i => f i v)) :
    Module.finrank (ZMod 3)
      (primeActionCharacters (A := B) (G := Multiplicative V) 3
        (representationGroupAction ρ)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine (representationCharacterHead_le_coordinates W ρ
    (fun i => @ternarySignRepresentation B (W i) _ _ _ (χ i))
      (fun _ => 0) ?_ f hf).trans ?_
  · intro i S
    rw [signScalar_subrepresentation_characterHead_eq_zero
      (A := W i) (χ i) (hχ i) S]
  · simp only [Finset.sum_const_zero]
    omega

/-- A quotient of a coordinate-separated ternary sign module still has zero
invariant-character head.  Invariant forms pull back along the supplied
actual equivariant surjection, so no equivariant section is required. -/
theorem representationQuotientCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    {V Q ι : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Fintype ι]
    [AddCommGroup Q] [Module (ZMod 3) Q]
    (W : ι → Type)
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 3) (W i)]
    [∀ i, FiniteDimensional (ZMod 3) (W i)]
    (ρ : Representation (ZMod 3) B V) (σ : Representation (ZMod 3) B Q)
    (χ : ∀ _ : ι, B →* Multiplicative (ZMod 2))
    (hχ : ∀ i, χ i ≠ 1)
    (f : ∀ i, ρ.IntertwiningMap (@ternarySignRepresentation B (W i) _ _ _ (χ i)))
    (hf : Function.Injective (fun v i => f i v))
    (q : ρ.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 3)
      (primeActionCharacters (A := B) (G := Multiplicative Q) 3
        (representationGroupAction σ)) = 0 := by
  have hsource := representationCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    W ρ χ hχ f hf
  have hquotient := representationQuotientCharacterHead_le_source ρ σ q hq
  rw [hsource] at hquotient
  exact Nat.eq_zero_of_le_zero hquotient

/-- Exact subquotient interface for the block-kernel application.  The
ambient coordinate maps restrict to the actual retained subrepresentation,
and every actual equivariant quotient of it has zero ternary head. -/
theorem subrepresentationQuotientCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    {V Q ι : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Fintype ι]
    [AddCommGroup Q] [Module (ZMod 3) Q]
    (W : ι → Type)
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 3) (W i)]
    [∀ i, FiniteDimensional (ZMod 3) (W i)]
    (ρ : Representation (ZMod 3) B V) (M : Subrepresentation ρ)
    (σ : Representation (ZMod 3) B Q)
    (χ : ∀ _ : ι, B →* Multiplicative (ZMod 2))
    (hχ : ∀ i, χ i ≠ 1)
    (f : ∀ i, ρ.IntertwiningMap (@ternarySignRepresentation B (W i) _ _ _ (χ i)))
    (hf : Function.Injective (fun v i => f i v))
    (q : M.toRepresentation.IntertwiningMap σ) (hq : Function.Surjective q) :
    Module.finrank (ZMod 3)
      (primeActionCharacters (A := B) (G := Multiplicative Q) 3
        (representationGroupAction σ)) = 0 := by
  let inclusion : M.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := M.toSubmodule.subtype
    isIntertwining' := fun _ => rfl
  }
  let fM : ∀ i, M.toRepresentation.IntertwiningMap
      (@ternarySignRepresentation B (W i) _ _ _ (χ i)) :=
    fun i => (f i).comp inclusion
  have hfM : Function.Injective (fun v i => fM i v) := by
    intro v w hvw
    apply Subtype.ext
    apply hf
    funext i
    exact congrFun hvw i
  exact representationQuotientCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    W M.toRepresentation σ χ hχ fM hfM q hq

end SymmetricSubgroupAsymptotics

end
