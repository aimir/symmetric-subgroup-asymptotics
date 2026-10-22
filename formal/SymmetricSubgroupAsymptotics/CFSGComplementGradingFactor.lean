import Mathlib.Algebra.Group.Subgroup.Basic

/-! A factorization is detected by two subgroups with trivial
intersection. This will be applied to the strict and preserving blocks
of the SAME lattice grading, not to eigenvalues in the field. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGComplementGradingFactor
variable {G : Type*} [Group G]

theorem mem_left_of_factor {V W L C : Subgroup G} (hVL : V≤L) (hWC : W≤C)
    (hLC : L⊓C=⊥) {g v u : G} (hv : v∈V) (hu : u∈W)
    (he : g=v*u) (hg : g∈L) : g∈V := by
  have huL : u∈L := by
    have hh := L.mul_mem (L.inv_mem (hVL hv)) hg
    simpa only [he,inv_mul_cancel_left] using hh
  have huone : u=1 := by
    have hh : u∈L⊓C := ⟨huL,hWC hu⟩
    rwa [hLC,Subgroup.mem_bot] at hh
  rw [he,huone,mul_one]
  exact hv

theorem mem_right_of_factor {V W L C : Subgroup G} (hVL : V≤L) (hWC : W≤C)
    (hLC : L⊓C=⊥) {g v u : G} (hv : v∈V) (hu : u∈W)
    (he : g=v*u) (hg : g∈C) : g∈W := by
  have hvC : v∈C := by
    have hh := C.mul_mem hg (C.inv_mem (hWC hu))
    simpa only [he,mul_inv_cancel_right] using hh
  have hvone : v=1 := by
    have hh : v∈L⊓C := ⟨hVL hv,hvC⟩
    rwa [hLC,Subgroup.mem_bot] at hh
  rw [he,hvone,one_mul]
  exact hu

end SymmetricSubgroupAsymptotics.CFSGComplementGradingFactor
