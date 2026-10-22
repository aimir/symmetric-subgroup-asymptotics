import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingRank
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The alternating form of three totally singular subspaces is built
on their actual sum-kernel. Its even rank will give intersection parity
once its actual kernel and dimension are computed. This file does not
assume that parity or a Dickson homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularTriangle
open CFSGOrthogonalDIndexAlternatingRank
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def tripleX (P L M : Submodule K V) : P × (L × M) →ₗ[K] V :=
  P.subtype.comp (LinearMap.fst K P (L × M))

def tripleY (P L M : Submodule K V) : P × (L × M) →ₗ[K] V :=
  L.subtype.comp ((LinearMap.fst K L M).comp (LinearMap.snd K P (L × M)))

def tripleZ (P L M : Submodule K V) : P × (L × M) →ₗ[K] V :=
  M.subtype.comp ((LinearMap.snd K L M).comp (LinearMap.snd K P (L × M)))

def sumHom (P L M : Submodule K V) : P × (L × M) →ₗ[K] V :=
  tripleX P L M + tripleY P L M + tripleZ P L M

def triangleSpace (P L M : Submodule K V) : Submodule K (P × (L × M)) :=
  (sumHom P L M).ker

def triangleX (P L M : Submodule K V) : triangleSpace P L M →ₗ[K] V :=
  (tripleX P L M).comp (triangleSpace P L M).subtype

def triangleY (P L M : Submodule K V) : triangleSpace P L M →ₗ[K] V :=
  (tripleY P L M).comp (triangleSpace P L M).subtype

def triangleZ (P L M : Submodule K V) : triangleSpace P L M →ₗ[K] V :=
  (tripleZ P L M).comp (triangleSpace P L M).subtype

theorem triangle_sum (P L M : Submodule K V) (w : triangleSpace P L M) :
    triangleX P L M w + triangleY P L M w + triangleZ P L M w = 0 :=
  w.property

def triangleForm (Q : QuadraticForm K V) (P L M : Submodule K V) :
    LinearMap.BilinForm K (triangleSpace P L M) :=
  Q.polarBilin.compl₁₂ (triangleX P L M) (triangleY P L M)

theorem triangleForm_isAlt (Q : QuadraticForm K V) (P L M : Submodule K V)
    (hP : ∀ x : P, Q (x : V) = 0) (hL : ∀ x : L, Q (x : V) = 0)
    (hM : ∀ x : M, Q (x : V) = 0) : (triangleForm Q P L M).IsAlt := by
  intro w
  have hs : (w.val.1 : V) + (w.val.2.1 : V) = -(w.val.2.2 : V) := by
    apply eq_neg_iff_add_eq_zero.mpr
    exact triangle_sum P L M w
  change QuadraticMap.polar Q (w.val.1 : V) (w.val.2.1 : V) = 0
  rw [QuadraticMap.polar, hs, Q.map_neg, hM w.val.2.2, hP w.val.1, hL w.val.2.1]
  simp only [sub_zero]

theorem triangleForm_rank_even [FiniteDimensional K V] (Q : QuadraticForm K V)
    (P L M : Submodule K V)
    (hP : ∀ x : P, Q (x : V) = 0) (hL : ∀ x : L, Q (x : V) = 0)
    (hM : ∀ x : M, Q (x : V) = 0) :
    Even (Module.finrank K (triangleForm Q P L M).range) :=
  even_finrank_range _ (triangleForm_isAlt Q P L M hP hL hM)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularTriangle
