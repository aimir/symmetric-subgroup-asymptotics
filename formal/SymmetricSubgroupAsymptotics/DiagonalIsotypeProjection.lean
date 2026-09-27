import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Set.Finite.Range

/-!
# Exact isotype projections for a finite diagonal coordinate family

An invariant subspace of a finite diagonal coordinate module splits by
equality of the actual scalar functions. Coordinates carrying the same
function remain in one component, with arbitrary correlations inside it.
The acting source need not be finite or even carry a group structure.

The proof multiplies separating diagonal filters. Thus it uses no
semisimplicity hypothesis, character orthogonality input, or product-kernel
assumption. Reconstruction sums over distinct scalar labels, never over
their possibly characteristic-divisible coordinate multiplicities.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.DiagonalIsotypeProjection

variable {k ι J : Type*} [Field k] (scalar : ι → J → k)

/-- One operator of the actual diagonal scalar family. -/
def diagonalOperator (g : J) : (ι → k) →ₗ[k] (ι → k) where
  toFun v i := scalar i g * v i
  map_add' v w := by
    funext i
    exact mul_add (scalar i g) (v i) (w i)
  map_smul' c v := by
    funext i
    change scalar i g * (c * v i) = c * (scalar i g * v i)
    exact mul_left_comm _ _ _

@[simp] theorem diagonalOperator_apply (g : J) (v : ι → k) (i : ι) :
    diagonalOperator scalar g v i = scalar i g * v i := rfl

/-- Labels are distinct actual scalar functions, not coordinate indices. -/
abbrev CharacterLabel : Type _ := Set.range scalar

instance characterLabelFintype [Fintype ι] : Fintype (CharacterLabel scalar) :=
  Fintype.ofFinite _

def coordinateLabel (i : ι) : CharacterLabel scalar := ⟨scalar i, ⟨i, rfl⟩⟩

/-- Projection onto all original coordinates with this one scalar label. -/
def isotypeProjection (χ : CharacterLabel scalar) : (ι → k) →ₗ[k] (ι → k) where
  toFun v i := if scalar i = χ.1 then v i else 0
  map_add' v w := by
    funext i
    by_cases hi : scalar i = χ.1 <;> simp [hi]
  map_smul' c v := by
    funext i
    by_cases hi : scalar i = χ.1 <;> simp [hi]

@[simp] theorem isotypeProjection_apply (χ : CharacterLabel scalar) (v : ι → k) (i : ι) :
    isotypeProjection scalar χ v i = if scalar i = χ.1 then v i else 0 := rfl

private theorem exists_separating_point (χ : CharacterLabel scalar) (i : ι)
    (hi : scalar i ≠ χ.1) : ∃ g : J, scalar i g ≠ χ.1 g := by
  by_contra h
  apply hi
  funext g
  by_contra hg
  exact h ⟨g, hg⟩

private def separatingPoint (χ : CharacterLabel scalar) (i : ι) (hi : scalar i ≠ χ.1) : J :=
  Classical.choose (exists_separating_point scalar χ i hi)

private theorem separatingPoint_spec (χ : CharacterLabel scalar) (i : ι)
    (hi : scalar i ≠ χ.1) :
    scalar i (separatingPoint scalar χ i hi) ≠ χ.1 (separatingPoint scalar χ i hi) :=
  Classical.choose_spec (exists_separating_point scalar χ i hi)

/-- A diagonal filter fixing the chosen label and killing coordinate i
when its label differs. No choice is needed for an equal-label coordinate. -/
private def separatingFactor (χ : CharacterLabel scalar) (i j : ι) : k :=
  if hi : scalar i = χ.1 then 1 else
    let g := separatingPoint scalar χ i hi
    (χ.1 g - scalar i g)⁻¹ * (scalar j g - scalar i g)

private theorem separatingFactor_one (χ : CharacterLabel scalar) (i j : ι)
    (hj : scalar j = χ.1) : separatingFactor scalar χ i j = 1 := by
  by_cases hi : scalar i = χ.1
  · simp only [separatingFactor, dif_pos hi]
  · simp only [separatingFactor, dif_neg hi, hj]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (separatingPoint_spec scalar χ i hi).symm)

private theorem separatingFactor_self_zero (χ : CharacterLabel scalar) (i : ι)
    (hi : scalar i ≠ χ.1) : separatingFactor scalar χ i i = 0 := by
  simp only [separatingFactor, dif_neg hi, sub_self, mul_zero]

private theorem separatingFactor_mul_mem (χ : CharacterLabel scalar)
    (K : Submodule k (ι → k))
    (hK : ∀ g v, v ∈ K → diagonalOperator scalar g v ∈ K)
    (i : ι) (v : ι → k) (hv : v ∈ K) :
    (fun j => separatingFactor scalar χ i j * v j) ∈ K := by
  by_cases hi : scalar i = χ.1
  · simpa only [separatingFactor, dif_pos hi, one_mul] using hv
  · let g := separatingPoint scalar χ i hi
    have he : (fun j => separatingFactor scalar χ i j * v j) =
        (χ.1 g - scalar i g)⁻¹ • (diagonalOperator scalar g v - scalar i g • v) := by
      funext j
      change separatingFactor scalar χ i j * v j =
        (χ.1 g - scalar i g)⁻¹ * (scalar j g * v j - scalar i g * v j)
      simp only [separatingFactor, dif_neg hi]
      change ((χ.1 g - scalar i g)⁻¹ * (scalar j g - scalar i g)) * v j = _
      rw [mul_assoc, sub_mul]
    rw [he]
    exact K.smul_mem _ (K.sub_mem (hK g v hv) (K.smul_mem _ hv))

private theorem separatingProduct_mul_mem (χ : CharacterLabel scalar)
    (K : Submodule k (ι → k))
    (hK : ∀ g v, v ∈ K → diagonalOperator scalar g v ∈ K)
    (s : Finset ι) (v : ι → k) (hv : v ∈ K) :
    (fun j => (∏ i ∈ s, separatingFactor scalar χ i j) * v j) ∈ K := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, one_mul] using hv
  | @insert i s hi ih =>
      have hm := separatingFactor_mul_mem scalar χ K hK i _ ih
      simpa only [Finset.prod_insert hi, mul_assoc] using hm

/-- Every actual scalar isotype projection preserves the original
invariant subspace, with no assumption on the source J or multiplicities. -/
theorem isotypeProjection_mem [Fintype ι] (K : Submodule k (ι → k))
    (hK : ∀ g v, v ∈ K → diagonalOperator scalar g v ∈ K)
    (χ : CharacterLabel scalar) (v : ι → k) (hv : v ∈ K) :
    isotypeProjection scalar χ v ∈ K := by
  have he : (fun j => (∏ i : ι, separatingFactor scalar χ i j) * v j) =
      isotypeProjection scalar χ v := by
    funext j
    by_cases hj : scalar j = χ.1
    · have hf : ∀ i : ι, separatingFactor scalar χ i j = 1 :=
        fun i => separatingFactor_one scalar χ i j hj
      simp only [isotypeProjection_apply, if_pos hj, hf, Finset.prod_const_one, one_mul]
    · have hz : (∏ i : ι, separatingFactor scalar χ i j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (separatingFactor_self_zero scalar χ j hj)
      simp only [isotypeProjection_apply, if_neg hj, hz, zero_mul]
  rw [← he]
  exact separatingProduct_mul_mem scalar χ K hK Finset.univ v hv

theorem isotypeProjection_idempotent (χ : CharacterLabel scalar) (v : ι → k) :
    isotypeProjection scalar χ (isotypeProjection scalar χ v) = isotypeProjection scalar χ v := by
  funext i
  by_cases hi : scalar i = χ.1 <;> simp [hi]

/-- Distinct labels have disjoint coordinate support, even when each
label has arbitrarily many original coordinates. -/
theorem isotypeProjection_of_ne (χ ψ : CharacterLabel scalar) (hχψ : χ ≠ ψ) (v : ι → k) :
    isotypeProjection scalar χ (isotypeProjection scalar ψ v) = 0 := by
  funext i
  by_cases hi : scalar i = χ.1
  · have hj : scalar i ≠ ψ.1 := fun hj => hχψ (Subtype.ext (hi.symm.trans hj))
    simp only [isotypeProjection_apply, if_pos hi, if_neg hj, Pi.zero_apply]
  · simp only [isotypeProjection_apply, if_neg hi, Pi.zero_apply]

/-- Exact reconstruction uses each distinct scalar function once. In
particular it never divides by the number of coordinates of an isotype. -/
theorem sum_isotypeProjection [Fintype ι] (v : ι → k) :
    (∑ χ : CharacterLabel scalar, isotypeProjection scalar χ v) = v := by
  funext i
  rw [Finset.sum_apply]
  let χ : CharacterLabel scalar := coordinateLabel scalar i
  calc
    (∑ ψ : CharacterLabel scalar, isotypeProjection scalar ψ v i) =
        isotypeProjection scalar χ v i := by
      apply Finset.sum_eq_single χ
      · intro ψ _ hψ
        have hi : scalar i ≠ ψ.1 := by
          intro hi
          apply hψ
          apply Subtype.ext
          exact hi.symm
        simp only [isotypeProjection_apply, if_neg hi]
      · simp
    _ = v i := by simp [χ, coordinateLabel]

/-- Membership in the original invariant subspace is exactly membership
of every component in that same subspace, not in a larger product kernel. -/
theorem mem_iff_isotypeProjection_mem [Fintype ι] (K : Submodule k (ι → k))
    (hK : ∀ g v, v ∈ K → diagonalOperator scalar g v ∈ K) (v : ι → k) :
    v ∈ K ↔ ∀ χ : CharacterLabel scalar, isotypeProjection scalar χ v ∈ K := by
  constructor
  · intro hv χ
    exact isotypeProjection_mem scalar K hK χ v hv
  · intro hv
    rw [← sum_isotypeProjection scalar v]
    exact K.sum_mem (fun χ _ => hv χ)

end SymmetricSubgroupAsymptotics.DiagonalIsotypeProjection

end
