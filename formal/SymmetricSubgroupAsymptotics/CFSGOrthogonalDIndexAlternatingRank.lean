import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingEvenDimension

/-! Every alternating bilinear form has even rank, including in
characteristic two. A genuine complement to its actual kernel reduces
this to the proved nondegenerate even-dimension theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingRank
open CFSGOrthogonalDIndexAlternatingEvenDimension
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem even_finrank_sub_kernel (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) :
    Even (Module.finrank K V - Module.finrank K B.ker) := by
  classical
  let R := B.ker
  obtain ⟨P, hcomp⟩ := R.exists_isCompl
  have hzero : ∀ x ∈ P, ∀ y ∈ R, B x y = 0 := by
    intro x _ y hy
    have hz : B y = 0 := hy
    exact hAlt.isRefl y x (LinearMap.congr_fun hz x)
  have hker : (B.restrict P).ker = ⊥ := by
    rw [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint hcomp.symm.codisjoint hzero]
    apply bot_unique
    intro x hx
    have hz : x.val ∈ R ⊓ P := ⟨hx, x.property⟩
    rw [hcomp.inf_eq_bot] at hz
    change x = 0
    apply Subtype.ext
    simpa using hz
  have hsep : ∀ x : P, (∀ y : P, (B.restrict P) x y = 0) → x = 0 := by
    intro x hx
    have hz : x ∈ (B.restrict P).ker := by
      change (B.restrict P) x = 0
      ext y
      exact hx y
    rw [hker] at hz
    simpa using hz
  have hP : (B.restrict P).Nondegenerate :=
    ⟨hsep, fun x hx => hsep x (fun y => hAlt.isRefl y.val x.val (hx y))⟩
  have hPalt : (B.restrict P).IsAlt := fun x => hAlt x.val
  have hEven := even_finrank_of_nondegenerate K (B.restrict P) hPalt hP
  have hdim := Submodule.finrank_add_eq_of_isCompl hcomp
  have heq : Module.finrank K V - Module.finrank K B.ker = Module.finrank K P := by
    have hdim' : Module.finrank K B.ker + Module.finrank K P = Module.finrank K V := hdim
    have hbound : Module.finrank K B.ker ≤ Module.finrank K V := Submodule.finrank_le _
    omega
  rw [heq]
  exact hEven

theorem even_finrank_range (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) :
    Even (Module.finrank K B.range) := by
  have hd := LinearMap.finrank_range_add_finrank_ker B
  have he : Module.finrank K B.range = Module.finrank K V - Module.finrank K B.ker := by omega
  rw [he]
  exact even_finrank_sub_kernel B hAlt

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAlternatingRank
