import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Max

/-! A finite kernel-coset signature separates selected quotient states.
It is computed only from the displayed kernel elements and point codes. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature
variable {R G : Type} [Group R] [Group G] [Fintype R]
  (kappa : R →* G) (code : G → ℕ)

def codes (g : G) : Finset ℕ := Finset.univ.image (fun r => code (g*kappa r))

private theorem codes_nonempty (g : G) : (codes kappa code g).Nonempty :=
  ⟨code (g*kappa 1),Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩⟩

def signature (g : G) : ℕ := (codes kappa code g).min' (codes_nonempty kappa code g)

theorem codes_mul (g : G) (r : R) :
    codes kappa code (g*kappa r)=codes kappa code g := by
  ext n
  constructor
  · intro hn
    obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨r*s,Finset.mem_univ _,by
      simpa only [map_mul,mul_assoc] using he⟩
  · intro hn
    obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨r⁻¹*s,Finset.mem_univ _,by
      simpa only [map_mul,map_inv,mul_assoc,mul_inv_cancel_left] using he⟩

theorem signature_mul (g : G) (r : R) :
    signature kappa code (g*kappa r)=signature kappa code g := by
  unfold signature
  simp only [codes_mul]

/-- Equality in the actual quotient forces equality of signatures. -/
theorem signature_eq_of_quotient_eq [kappa.range.Normal] {g h : G}
    (he : QuotientGroup.mk' kappa.range g=QuotientGroup.mk' kappa.range h) :
    signature kappa code g=signature kappa code h := by
  have hm : h⁻¹*g ∈ kappa.range := (QuotientGroup.eq_one_iff _).mp (by
    change QuotientGroup.mk' kappa.range (h⁻¹*g)=1
    rw [map_mul,map_inv,he,inv_mul_cancel])
  obtain ⟨r,hr⟩ := hm
  have hg : g=h*kappa r := by rw [hr]; simp
  rw [hg,signature_mul]
end SymmetricSubgroupAsymptotics.FiniteKernelCosetSignature
