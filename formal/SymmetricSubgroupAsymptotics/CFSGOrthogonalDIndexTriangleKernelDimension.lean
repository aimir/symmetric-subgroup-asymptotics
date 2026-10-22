import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleRadical

/-! The actual triangle radical has dimension equal to the sum of
the three pair-intersection dimensions minus the triple intersection.
Its first-component kernel is identified by a genuine injective second
projection, with image exactly L intersect M. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleKernelDimension
open CFSGOrthogonalDIndexSingularTriangle CFSGOrthogonalDIndexTriangleRadical
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def radicalKernelY (Q : QuadraticForm K V) (P L M : Submodule K V) :
    (radicalX Q P L M).ker →ₗ[K] V :=
  (triangleY P L M).comp
    ((triangleForm Q P L M).ker.subtype.comp (radicalX Q P L M).ker.subtype)

theorem radicalKernelY_injective (Q : QuadraticForm K V) (P L M : Submodule K V) :
    Function.Injective (radicalKernelY Q P L M) := by
  intro x y h
  have hx0 : triangleX P L M x.val.val = 0 := x.property
  have hy0 : triangleX P L M y.val.val = 0 := y.property
  change triangleY P L M x.val.val = triangleY P L M y.val.val at h
  have hsx := triangle_sum P L M x.val.val
  have hsy := triangle_sum P L M y.val.val
  rw [hx0, zero_add] at hsx
  rw [hy0, zero_add, ← h] at hsy
  have hz : triangleZ P L M x.val.val = triangleZ P L M y.val.val :=
    add_left_cancel (hsx.trans hsy.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hx0.trans hy0.symm
  · apply Prod.ext
    · apply Subtype.ext
      exact h
    · apply Subtype.ext
      exact hz

theorem radicalKernelY_range (Q : QuadraticForm K V) (P L M : Submodule K V) :
    (radicalKernelY Q P L M).range = L ⊓ M := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    change triangleY P L M w.val.val ∈ L ⊓ M
    refine ⟨w.val.val.val.2.1.property, ?_⟩
    have hx : triangleX P L M w.val.val = 0 := w.property
    have hs := triangle_sum P L M w.val.val
    rw [hx, zero_add] at hs
    have he : triangleY P L M w.val.val = -triangleZ P L M w.val.val :=
      eq_neg_iff_add_eq_zero.mpr hs
    rw [he]
    exact M.neg_mem w.val.val.val.2.2.property
  · rintro ⟨hyL, hyM⟩
    let t : triangleSpace P L M :=
      ⟨((0 : P), (⟨y, hyL⟩, ⟨-y, M.neg_mem hyM⟩)), by
        change (0 : V) + y + -y = 0
        simp only [zero_add, add_neg_cancel]⟩
    have ht : t ∈ (triangleForm Q P L M).ker := by
      change triangleForm Q P L M t = 0
      apply LinearMap.ext
      intro u
      change Q.polarBilin 0 (triangleY P L M u) = 0
      simp only [LinearMap.BilinForm.zero_left]
    let a : (triangleForm Q P L M).ker := ⟨t, ht⟩
    have ha : a ∈ (radicalX Q P L M).ker := by
      change (0 : V) = 0
      rfl
    exact ⟨⟨a, ha⟩, rfl⟩

theorem radicalX_kernel_finrank [FiniteDimensional K V]
    (Q : QuadraticForm K V) (P L M : Submodule K V) :
    Module.finrank K (radicalX Q P L M).ker = Module.finrank K ↥(L ⊓ M) := by
  have h := (LinearEquiv.ofInjective (radicalKernelY Q P L M)
    (radicalKernelY_injective Q P L M)).finrank_eq
  rw [radicalKernelY_range] at h
  exact h

theorem triangle_kernel_finrank [FiniteDimensional K V]
    (Q : QuadraticForm K V) (P L M : Submodule K V)
    (hQ : Q.polarBilin.Nondegenerate)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) (hL : LinearMap.BilinForm.orthogonal Q.polarBilin L = L)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M) :
    Module.finrank K (triangleForm Q P L M).ker + Module.finrank K ↥(P ⊓ L ⊓ M) =
      Module.finrank K ↥(P ⊓ L) + Module.finrank K ↥(L ⊓ M) +
        Module.finrank K ↥(P ⊓ M) := by
  let R := (triangleForm Q P L M).ker
  let f : R →ₗ[K] V := radicalX Q P L M
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := K) (V := R) (V₂ := V) f
  change Module.finrank K (radicalX Q P L M).range +
    Module.finrank K (radicalX Q P L M).ker =
      Module.finrank K (triangleForm Q P L M).ker at hrn
  rw [radicalX_range Q P L M hQ hP hL hM, radicalX_kernel_finrank] at hrn
  have hi : (P ⊓ L) ⊓ (P ⊓ M) = P ⊓ L ⊓ M := by
    ext x
    constructor
    · rintro ⟨⟨hp, hl⟩, ⟨_, hm⟩⟩
      exact ⟨⟨hp, hl⟩, hm⟩
    · rintro ⟨⟨hp, hl⟩, hm⟩
      exact ⟨⟨hp, hl⟩, ⟨hp, hm⟩⟩
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ L) (P ⊓ M)
  rw [hi] at hs
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTriangleKernelDimension
