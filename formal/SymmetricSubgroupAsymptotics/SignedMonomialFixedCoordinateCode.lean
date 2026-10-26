import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Group.Units.Basic

/-! Literal monomial fixed-vector geometry. A fixed vector determines
all scalar coefficients on its nonzero support. Only the zero-coordinate
coefficients and the original permutation remain in a faithful code.
The scalars are arbitrary units: no unsigned lift or splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SignedMonomialFixedCoordinateCode

variable {G I K : Type*} [Group G] [Field K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))

include hformula in
theorem fixed_support_iff (g : G) (v : I → K) (hg : ρ g v=v) (i : I) :
    v (t g i)≠0 ↔ v i≠0 := by
  have h := congrFun hg (t g i)
  rw [hformula,Equiv.symm_apply_apply] at h
  rw [←h,mul_ne_zero_iff]
  exact ⟨fun h => h.2,fun h => ⟨(a g (t g i)).ne_zero,h⟩⟩

include hformula in
theorem fixed_element_eq_of_zero_coefficients
    (hρ : Function.Injective ρ) (v : I → K) (g h : G)
    (hg : ρ g v=v) (hh : ρ h v=v) (ht : t g=t h)
    (hzero : ∀ i,v i=0 → a g i=a h i) : g=h := by
  have hcoeff : ∀ i,a g i=a h i := by
    intro i
    by_cases hi : v i=0
    · exact hzero i hi
    · have hgv := congrFun hg i
      have hhv := congrFun hh i
      rw [hformula] at hgv hhv
      rw [←ht] at hhv
      have hx : v ((t g).symm i)≠0 := by
        intro hx
        exact hi (by simpa only [hx,mul_zero] using hgv.symm)
      apply Units.ext
      exact mul_right_cancel₀ hx (hgv.trans hhv.symm)
  apply hρ
  ext w i
  rw [hformula,hformula,ht,hcoeff]

def fixedCoordinateCode (v : I → K) (g : {g : G // ρ g v=v}) :
    ({i : I // v i=0} → Kˣ) × Equiv.Perm I :=
  (fun i => a g.val i.val,t g.val)

include hformula in
theorem fixedCoordinateCode_injective
    (hρ : Function.Injective ρ) (v : I → K) :
    Function.Injective (fixedCoordinateCode ρ t a v) := by
  rintro ⟨g,hg⟩ ⟨h,hh⟩ he
  apply Subtype.ext
  apply fixed_element_eq_of_zero_coefficients ρ t a hformula hρ v g h hg hh
  · exact congrArg Prod.snd he
  · intro i hi
    exact congrFun (congrArg Prod.fst he) ⟨i,hi⟩

end SymmetricSubgroupAsymptotics.SignedMonomialFixedCoordinateCode
