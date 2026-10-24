import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex
import Mathlib.Tactic.Abel

/-! A projected subgroup fixing a vector preserves the affine value-one
slice of the actual kernel's annihilator. Exact fibre counting retains
the base-field factor. This is not a prime multiplier asserted for an
arbitrary abelian radical: fixed-vector and SAME-subgroup invariance
are explicit and are used in the proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.InvariantAnnihilatorEvaluationSliceOrbitIndex

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

private def linearSplitEquiv (E : A →ₗ[F] F) (u : A) (hu : E u = 1) :
    A ≃ F × E.ker where
  toFun x := ⟨E x, ⟨x-E x • u, by simp [map_sub, map_smul, hu]⟩⟩
  invFun p := p.2.val+p.1 • u
  left_inv x := by dsimp; abel
  right_inv p := by
    rcases p with ⟨c,k,hk⟩
    have hk' : E k = 0 := hk
    apply Prod.ext
    · simp [map_add, map_smul, hk', hu]
    · apply Subtype.ext
      simp [map_add, map_smul, hk', hu]

private def linearFibreEquivKer (E : A →ₗ[F] F) (u : A) (hu : E u = 1) :
    {x : A // E x = 1} ≃ E.ker where
  toFun x := ⟨x.val-u, by simp [map_sub, x.property, hu]⟩
  invFun k := ⟨k.val+u, by simp [map_add, hu]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp

private theorem linear_fibre_card_mul [Finite F] [Finite A]
    (E : A →ₗ[F] F) (u : A) (hu : E u = 1) :
    Nat.card F * Nat.card {x : A // E x = 1} = Nat.card A := by
  have hs := Nat.card_congr (linearSplitEquiv E u hu)
  rw [Nat.card_prod] at hs
  have hf := Nat.card_congr (linearFibreEquivKer E u hu)
  rw [hf]
  exact hs.symm

variable {V G : Type*} [AddCommGroup V] [Module F V] [Group G]

/-- This is a literal affine slice in the actual annihilator. -/
def evaluationSlice (J : Submodule F V) (z : V) : Set (Module.Dual F V) :=
  {φ | φ ∈ J.dualAnnihilator ∧ φ z = 1}

private def evaluationMap (J : Submodule F V) (z : V) :
    J.dualAnnihilator →ₗ[F] F where
  toFun φ := φ.val z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_annihilator_eq_one_on (J : Submodule F V) (z : V) (hz : z ∉ J) :
    ∃ φ : J.dualAnnihilator, φ.val z = 1 := by
  obtain ⟨φ,hφ⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on J z hz
  refine ⟨(φ.val z)⁻¹ • φ, ?_⟩
  change (φ.val z)⁻¹ * φ.val z = 1
  exact inv_mul_cancel₀ hφ

private theorem evaluation_fibre_card_mul [Finite F] [Finite (Module.Dual F V)]
    (J : Submodule F V) (z : V) (φ : J.dualAnnihilator) (hφ : φ.val z = 1) :
    Nat.card F * Nat.card {ψ : J.dualAnnihilator // evaluationMap J z ψ = 1} =
      Nat.card J.dualAnnihilator := by
  letI : Finite J.dualAnnihilator :=
    Finite.of_injective (fun ψ : J.dualAnnihilator => ψ.val) Subtype.val_injective
  have hvalue : evaluationMap J z φ = 1 := hφ
  exact linear_fibre_card_mul (F := F) (A := J.dualAnnihilator)
    (evaluationMap J z) φ hvalue

theorem card_evaluationSlice_mul [Finite F] [Module.Finite F V]
    (J : Submodule F V) (z : V) (φ : J.dualAnnihilator) (hφ : φ.val z = 1) :
    Nat.card F * Nat.card (evaluationSlice J z) = Nat.card (V ⧸ J) := by
  letI : Finite (Module.Dual F V) := Module.finite_of_finite F
  let e : {ψ : J.dualAnnihilator // evaluationMap J z ψ = 1} ≃ evaluationSlice J z := {
    toFun ψ := ⟨ψ.val.val,ψ.val.property,ψ.property⟩
    invFun ψ := ⟨⟨ψ.val,ψ.property.1⟩,ψ.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  calc
    _ = Nat.card F * Nat.card {ψ : J.dualAnnihilator // evaluationMap J z ψ = 1} := by
      rw [Nat.card_congr e]
    _ = Nat.card J.dualAnnihilator := evaluation_fibre_card_mul J z φ hφ
    _ = Nat.card (V ⧸ J) :=
      (Nat.card_congr (Subspace.quotEquivAnnihilator J).toEquiv).symm

/-- The index is that of the SAME subgroup preserving J and fixing z.
The full group need not fix z; only the restricted orbit uses the slice. -/
theorem dual_orbit_mul_field_le_quotient_card_mul_index
    [Finite F] [Finite G] [Module.Finite F V]
    (ρ : G →* V ≃ₗ[F] V) (L : Subgroup G) (J : Submodule F V)
    (hJ : ∀ g ∈ L, ∀ v ∈ J, ρ g v ∈ J)
    (z : V) (hz : ∀ g ∈ L, ρ g z = z)
    (φ : J.dualAnnihilator) (hφ : φ.val z = 1) :
    Nat.card F * Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit ρ φ.val) ≤
      Nat.card (V ⧸ J) * L.index := by
  letI : MulAction G (Module.Dual F V) := InvariantAnnihilatorOrbitIndex.dualAction ρ
  letI : Finite (Module.Dual F V) := Module.finite_of_finite F
  have hA : ∀ g : L, ∀ ψ ∈ evaluationSlice J z,
      g • ψ ∈ evaluationSlice J z := by
    intro g ψ hψ
    change ψ.comp (ρ g.val⁻¹).toLinearMap ∈ J.dualAnnihilator ∧
      (ψ.comp (ρ g.val⁻¹).toLinearMap) z = 1
    constructor
    · have hAnn := hψ.1
      rw [Submodule.mem_dualAnnihilator] at hAnn ⊢
      intro v hv
      exact hAnn _ (hJ g.val⁻¹ (L.inv_mem g.property) v hv)
    · change ψ (ρ g.val⁻¹ z) = 1
      rw [hz g.val⁻¹ (L.inv_mem g.property)]
      exact hψ.2
  have ho := SubgroupInvariantSetOrbitIndex.orbit_card_le_invariant_set_mul_index
    L (evaluationSlice J z) φ.val ⟨φ.property,hφ⟩ hA
  have ho' : Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit ρ φ.val) ≤
      Nat.card (evaluationSlice J z) * L.index := ho
  calc
    _ ≤ Nat.card F * (Nat.card (evaluationSlice J z) * L.index) :=
      Nat.mul_le_mul_left _ ho'
    _ = (Nat.card F * Nat.card (evaluationSlice J z)) * L.index := (Nat.mul_assoc _ _ _).symm
    _ = _ := by rw [card_evaluationSlice_mul J z φ hφ]

end SymmetricSubgroupAsymptotics.InvariantAnnihilatorEvaluationSliceOrbitIndex
