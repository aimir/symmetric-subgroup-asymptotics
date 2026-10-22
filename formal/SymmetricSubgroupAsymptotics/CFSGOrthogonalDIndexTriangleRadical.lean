import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleDimensions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOrthogonalLattice

/-! The actual kernel of the singular-triangle form is characterized
by its first component. For three self-orthogonal spaces it is exactly
the sum of the two genuine pair intersections in that component. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleRadical
open CFSGOrthogonalDIndexSingularTriangle CFSGOrthogonalDIndexTriangleDimensions
open CFSGOrthogonalDIndexOrthogonalLattice
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem triangleForm_kernel_iff (Q : QuadraticForm K V) (P L M : Submodule K V)
    (w : triangleSpace P L M) :
    w ∈ (triangleForm Q P L M).ker ↔
      triangleX P L M w ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (L ⊓ (P ⊔ M)) := by
  constructor
  · intro hw y hy
    rw [← triangleY_range] at hy
    obtain ⟨v, rfl⟩ := hy
    have hz := LinearMap.congr_fun hw v
    change Q.polarBilin (triangleX P L M w) (triangleY P L M v) = 0 at hz
    change Q.polarBilin (triangleY P L M v) (triangleX P L M w) = 0
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hz
  · intro hw
    change triangleForm Q P L M w = 0
    apply LinearMap.ext
    intro v
    have hy : triangleY P L M v ∈ L ⊓ (P ⊔ M) := by
      rw [← triangleY_range]
      exact ⟨v, rfl⟩
    have hz := hw (triangleY P L M v) hy
    change Q.polarBilin (triangleX P L M w) (triangleY P L M v) = 0
    change QuadraticMap.polar Q (triangleY P L M v) (triangleX P L M w) = 0 at hz
    exact (QuadraticMap.polar_comm Q (triangleX P L M w) (triangleY P L M v)).trans hz

theorem mem_intersection_sum_iff (P L M : Submodule K V) (x : V) (hx : x ∈ P) :
    x ∈ L ⊔ (P ⊓ M) ↔ x ∈ (P ⊓ L) ⊔ (P ⊓ M) := by
  constructor
  · intro h
    obtain ⟨l, hl, c, hc, he⟩ := Submodule.mem_sup.mp h
    have heq : x - c = l := by rw [← he]; abel
    have hlP : l ∈ P := by
      have hsub := P.sub_mem hx hc.1
      simpa only [heq] using hsub
    exact Submodule.mem_sup.mpr ⟨l, ⟨hlP, hl⟩, c, hc, he⟩
  · intro h
    obtain ⟨l, hl, c, hc, he⟩ := Submodule.mem_sup.mp h
    exact Submodule.mem_sup.mpr ⟨l, hl.2, c, hc, he⟩

theorem triangleForm_kernel_iff_pair_sum [FiniteDimensional K V]
    (Q : QuadraticForm K V) (P L M : Submodule K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) (hL : LinearMap.BilinForm.orthogonal Q.polarBilin L = L)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M) (w : triangleSpace P L M) :
    w ∈ (triangleForm Q P L M).ker ↔
      triangleX P L M w ∈ (P ⊓ L) ⊔ (P ⊓ M) := by
  have hRefl : Q.polarBilin.IsRefl := by
    intro x y h
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h
  rw [triangleForm_kernel_iff,
    middle_range_orthogonal Q.polarBilin hQ hRefl P L M hP hL hM]
  exact mem_intersection_sum_iff P L M _ w.val.1.property

def radicalX (Q : QuadraticForm K V) (P L M : Submodule K V) :
    (triangleForm Q P L M).ker →ₗ[K] V :=
  (triangleX P L M).comp (triangleForm Q P L M).ker.subtype

theorem radicalX_range [FiniteDimensional K V]
    (Q : QuadraticForm K V) (P L M : Submodule K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) (hL : LinearMap.BilinForm.orthogonal Q.polarBilin L = L)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M) :
    (radicalX Q P L M).range = (P ⊓ L) ⊔ (P ⊓ M) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact (triangleForm_kernel_iff_pair_sum Q P L M hQ hP hL hM w.val).mp w.property
  · intro hx
    obtain ⟨a, ha, c, hc, he⟩ := Submodule.mem_sup.mp hx
    have hxP : x ∈ P := by rw [← he]; exact P.add_mem ha.1 hc.1
    have hz : x + -a + -c = 0 := by rw [← he]; abel
    let w : triangleSpace P L M :=
      ⟨(⟨x, hxP⟩, (⟨-a, L.neg_mem ha.2⟩, ⟨-c, M.neg_mem hc.2⟩)), hz⟩
    have hw : w ∈ (triangleForm Q P L M).ker :=
      (triangleForm_kernel_iff_pair_sum Q P L M hQ hP hL hM w).mpr hx
    exact ⟨⟨w, hw⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleRadical
