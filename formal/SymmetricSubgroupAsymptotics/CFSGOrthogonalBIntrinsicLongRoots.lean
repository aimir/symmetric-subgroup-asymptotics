import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentSylow
import SymmetricSubgroupAsymptotics.CFSGSylowCenterConjugacy

/-! The actual odd-B long-root elements, defined by literal conjugates
of the original highest root, are intrinsically the union of centres
of defining-characteristic Sylow subgroups. This does not identify
polar points or assert an automorphism classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGSylowCenterRecognition
variable {K : Type} [Field K] [Finite K]

def IsLongRootElement (s : ℕ) (x : elementaryRootGroup K (s + 3)) : Prop :=
  ∃ g : elementaryRootGroup K (s + 3), ∃ a : K, x = g * highestRoot s a * g⁻¹

theorem isLongRootElement_iff_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (x : elementaryRootGroup K (s + 3)) :
    IsLongRootElement s x ↔ x ∈ sylowCenterElements (G := elementaryRootGroup K (s + 3)) p := by
  constructor
  · rintro ⟨g, a, rfl⟩
    have hh : highestRoot (K := K) s a ∈
        sylowCenterElements (G := elementaryRootGroup K (s + 3)) p :=
      ⟨unipotentSylow K p (s + 2) h2,
        ⟨highestRoot s a, highestRoot_mem_unipotent h2 s a⟩,
        highestRoot_central p h2 s a, rfl⟩
    exact automorphism_mem_sylowCenterElements p (MulAut.conj g) hh
  · intro hx
    obtain ⟨g, z, hz, hg⟩ := exists_conjugate_fixed_sylow_center p
      (unipotentSylow K p (s + 2) h2) hx
    obtain ⟨a, ha⟩ := central_unipotent_is_highestRoot h2 s z hz
    exact ⟨g, a, hg.symm.trans (by rw [ha])⟩

theorem automorphism_isLongRootElement_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryRootGroup K (s + 3)))
    (x : elementaryRootGroup K (s + 3)) :
    IsLongRootElement s (f x) ↔ IsLongRootElement s x := by
  rw [isLongRootElement_iff_sylowCenterElements p h2,
    isLongRootElement_iff_sylowCenterElements p h2]
  exact automorphism_mem_sylowCenterElements_iff p f x

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
