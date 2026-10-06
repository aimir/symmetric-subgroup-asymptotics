import SymmetricSubgroupAsymptotics.DistinctDiagonalFullSubmodule

/-!
# Distinct diagonal characters on module-valued coordinates

The literal translation coordinates in an imprimitive affine action take
values in the local translation module, not canonically in its scalar field.
This file proves the distinct-character projector directly for functions
`ι → V`.  It therefore avoids choosing a basis of the one-dimensional local
module merely to apply the scalar-valued theorem.

The proof uses the same finite product of separating diagonal operators as
the scalar theorem.  Distinct characters isolate one original coordinate;
surjectivity of every coordinate projection then supplies every coordinate
vector, and their sum is the whole ambient function module.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace DiagonalInvariantSubmodules

variable {k ι J V : Type*} [Field k] [Fintype ι]
  [AddCommGroup V] [Module k V]

/-- One diagonal scalar operator on module-valued coordinates. -/
def diagonalModuleOperator (scalar : ι → J → k) (g : J) :
    (ι → V) →ₗ[k] (ι → V) where
  toFun v i := scalar i g • v i
  map_add' v w := by
    funext i
    exact smul_add (scalar i g) (v i) (w i)
  map_smul' c v := by
    funext i
    exact smul_comm (scalar i g) c (v i)

omit [Fintype ι] in
@[simp] theorem diagonalModuleOperator_apply
    (scalar : ι → J → k) (g : J) (v : ι → V) (i : ι) :
    diagonalModuleOperator scalar g v i = scalar i g • v i := rfl

/-- A submodule stable under the literal diagonal scalar family. -/
def ModuleStable (scalar : ι → J → k) :=
  {K : Submodule k (ι → V) //
    ∀ g v, v ∈ K → diagonalModuleOperator scalar g v ∈ K}

/-- Coordinatewise fullness for an arbitrary coordinate module. -/
def ModuleFullCoordinates (K : Submodule k (ι → V)) : Prop :=
  ∀ i, Function.Surjective (fun v : K => v.1 i)

omit [Field k] [Fintype ι] in
private theorem exists_moduleSeparatingPoint
    (scalar : ι → J → k) (i a : ι)
    (hia : scalar a ≠ scalar i) :
    ∃ g : J, scalar a g ≠ scalar i g := by
  by_contra h
  apply hia
  funext g
  by_contra hg
  exact h ⟨g, hg⟩

private def moduleSeparatingPoint
    (scalar : ι → J → k) (i a : ι)
    (hia : scalar a ≠ scalar i) : J :=
  Classical.choose (exists_moduleSeparatingPoint scalar i a hia)

omit [Field k] [Fintype ι] in
private theorem moduleSeparatingPoint_spec
    (scalar : ι → J → k) (i a : ι)
    (hia : scalar a ≠ scalar i) :
    scalar a (moduleSeparatingPoint scalar i a hia) ≠
      scalar i (moduleSeparatingPoint scalar i a hia) :=
  Classical.choose_spec (exists_moduleSeparatingPoint scalar i a hia)

/-- The factor which fixes the character at `i` and kills coordinate `a`
when its character differs. -/
private def moduleSeparatingFactor
    (scalar : ι → J → k) (i a j : ι) : k :=
  if hia : scalar a = scalar i then 1 else
    let g := moduleSeparatingPoint scalar i a hia
    (scalar i g - scalar a g)⁻¹ * (scalar j g - scalar a g)

omit [Fintype ι] in
private theorem moduleSeparatingFactor_one
    (scalar : ι → J → k) (i a j : ι)
    (hj : scalar j = scalar i) :
    moduleSeparatingFactor scalar i a j = 1 := by
  by_cases hia : scalar a = scalar i
  · simp only [moduleSeparatingFactor, dif_pos hia]
  · simp only [moduleSeparatingFactor, dif_neg hia, hj]
    exact inv_mul_cancel₀
      (sub_ne_zero.mpr (moduleSeparatingPoint_spec scalar i a hia).symm)

omit [Fintype ι] in
private theorem moduleSeparatingFactor_self_zero
    (scalar : ι → J → k) (i a : ι)
    (hia : scalar a ≠ scalar i) :
    moduleSeparatingFactor scalar i a a = 0 := by
  simp only [moduleSeparatingFactor, dif_neg hia, sub_self, mul_zero]

omit [Fintype ι] in
private theorem moduleSeparatingFactor_smul_mem
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (hK : ∀ g v, v ∈ K → diagonalModuleOperator scalar g v ∈ K)
    (i a : ι) (v : ι → V) (hv : v ∈ K) :
    (fun j => moduleSeparatingFactor scalar i a j • v j) ∈ K := by
  by_cases hia : scalar a = scalar i
  · simpa only [moduleSeparatingFactor, dif_pos hia, one_smul] using hv
  · let g := moduleSeparatingPoint scalar i a hia
    have he :
        (fun j => moduleSeparatingFactor scalar i a j • v j) =
          (scalar i g - scalar a g)⁻¹ •
            (diagonalModuleOperator scalar g v - scalar a g • v) := by
      funext j
      change moduleSeparatingFactor scalar i a j • v j =
        (scalar i g - scalar a g)⁻¹ •
          (scalar j g • v j - scalar a g • v j)
      simp only [moduleSeparatingFactor, dif_neg hia]
      rw [← sub_smul, smul_smul]
    rw [he]
    exact K.smul_mem _ (K.sub_mem (hK g v hv) (K.smul_mem _ hv))

omit [Fintype ι] in
private theorem moduleSeparatingProduct_smul_mem
    (scalar : ι → J → k)
    (K : Submodule k (ι → V))
    (hK : ∀ g v, v ∈ K → diagonalModuleOperator scalar g v ∈ K)
    (i : ι) (s : Finset ι) (v : ι → V) (hv : v ∈ K) :
    (fun j => (∏ a ∈ s, moduleSeparatingFactor scalar i a j) • v j) ∈ K := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, one_smul] using hv
  | @insert a s ha ih =>
      have hm := moduleSeparatingFactor_smul_mem scalar K hK i a _ ih
      simpa only [Finset.prod_insert ha, mul_smul] using hm

/-- The vector supported only at one original coordinate. -/
def singleCoordinate (i : ι) (v : ι → V) : ι → V :=
  fun j => if j = i then v j else 0

/-- Distinct literal characters make every single-coordinate projection
preserve the original stable submodule. -/
theorem singleCoordinate_mem_of_injective
    (scalar : ι → J → k)
    (hscalar : Function.Injective scalar)
    (K : ModuleStable (V := V) scalar)
    (i : ι) (v : ι → V) (hv : v ∈ K.1) :
    singleCoordinate i v ∈ K.1 := by
  have hproduct := moduleSeparatingProduct_smul_mem scalar K.1 K.2
    i Finset.univ v hv
  have he :
      (fun j => (∏ a : ι, moduleSeparatingFactor scalar i a j) • v j) =
        singleCoordinate i v := by
    funext j
    by_cases hji : j = i
    · have hone : ∀ a : ι,
          moduleSeparatingFactor scalar i a j = 1 := by
        intro a
        exact moduleSeparatingFactor_one scalar i a j
          (congrArg scalar hji)
      simp only [singleCoordinate, if_pos hji, hone,
        Finset.prod_const_one, one_smul]
    · have hchar : scalar j ≠ scalar i := fun h => hji (hscalar h)
      have hzero : (∏ a : ι,
          moduleSeparatingFactor scalar i a j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j)
          (moduleSeparatingFactor_self_zero scalar i j hchar)
      simp only [singleCoordinate, if_neg hji, hzero, zero_smul]
  rw [← he]
  exact hproduct

/-- Distinct diagonal characters and surjective projection onto every
module-valued coordinate force the whole correlated submodule to be the
ambient product. -/
theorem eq_top_of_moduleFullCoordinates_of_injective
    (scalar : ι → J → k)
    (hscalar : Function.Injective scalar)
    (K : ModuleStable (V := V) scalar)
    (hfull : ModuleFullCoordinates K.1) :
    K.1 = ⊤ := by
  apply top_unique
  intro v _hv
  have hsum : (∑ i : ι, singleCoordinate i v) = v := by
    funext j
    rw [Finset.sum_apply]
    simp [singleCoordinate]
  rw [← hsum]
  apply K.1.sum_mem
  intro i _hi
  obtain ⟨x, hx⟩ := hfull i (v i)
  have hsingle := singleCoordinate_mem_of_injective scalar hscalar K i x.1 x.2
  have he : singleCoordinate i x.1 = singleCoordinate i v := by
    funext j
    by_cases hji : j = i
    · subst j
      simpa only [singleCoordinate] using hx
    · simp only [singleCoordinate, if_neg hji]
  rw [← he]
  exact hsingle

end DiagonalInvariantSubmodules
end SymmetricSubgroupAsymptotics

end
