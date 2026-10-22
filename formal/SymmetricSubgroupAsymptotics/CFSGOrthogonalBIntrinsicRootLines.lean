import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootLineRecognition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots

/-! Every abstract automorphism of the SAME odd-B group preserves the
family of literal conjugate highest-root subgroups. The line is recovered
from any nonidentity root element by prime-power double-centralizer tests. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

def conjugateRootLine (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) : Subgroup (elementaryRootGroup K (s + 3)) :=
  (highestRootLine h2 s).map (MulAut.conj g).toMonoidHom

theorem mem_conjugateRootLine_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : elementaryRootGroup K (s + 3))
    (a : K) (ha : a ≠ 0) (y : elementaryRootGroup K (s + 3)) :
    y ∈ conjugateRootLine h2 s g ↔
      PrimePowerDoubleCentralizer p (g * highestRoot s a * g⁻¹) y := by
  let e := MulAut.conj g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (doubleCentralizer_map_iff p e (highestRoot s a) z).mpr
      ((mem_highestRootLine_iff_doubleCentralizer p h2 s a ha z).mp hz)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (mem_highestRootLine_iff_doubleCentralizer p h2 s a ha (e.symm y)).mpr
    apply (doubleCentralizer_map_iff p e (highestRoot s a) (e.symm y)).mp
    simpa only [e.apply_symm_apply] using hy

theorem automorphism_maps_conjugateRootLine (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryRootGroup K (s + 3)))
    (g : elementaryRootGroup K (s + 3)) :
    ∃ h : elementaryRootGroup K (s + 3),
      (conjugateRootLine h2 s g).map f.toMonoidHom = conjugateRootLine h2 s h := by
  have hx : IsLongRootElement s (g * highestRoot s 1 * g⁻¹) := ⟨g, 1, rfl⟩
  obtain ⟨h, a, he⟩ := (automorphism_isLongRootElement_iff p h2 s f _).mpr hx
  have hroot : highestRoot (K := K) s 1 ≠ 1 := by
    intro hz
    exact one_ne_zero (highestRoot_injective h2 s (hz.trans (highestRoot_zero h2 s).symm))
  have ha : a ≠ 0 := by
    intro hz
    have he0 : f (g * highestRoot s 1 * g⁻¹) = 1 := by
      rw [he, hz, highestRoot_zero h2 s, mul_one, mul_inv_cancel]
    have hc : g * highestRoot s 1 * g⁻¹ = 1 := f.injective (he0.trans f.map_one.symm)
    have hc' : highestRoot (K := K) s 1 = 1 :=
      (MulAut.conj g).injective (hc.trans (MulAut.conj g).map_one.symm)
    exact hroot hc'
  refine ⟨h, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (mem_conjugateRootLine_iff p h2 s h a ha (f z)).mpr
    rw [← he]
    exact (doubleCentralizer_map_iff p f (g * highestRoot s 1 * g⁻¹) z).mpr
      ((mem_conjugateRootLine_iff p h2 s g 1 one_ne_zero z).mp hz)
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    apply (mem_conjugateRootLine_iff p h2 s g 1 one_ne_zero (f.symm y)).mpr
    apply (doubleCentralizer_map_iff p f (g * highestRoot s 1 * g⁻¹) (f.symm y)).mp
    rw [f.apply_symm_apply, he]
    exact (mem_conjugateRootLine_iff p h2 s h a ha y).mp hy

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
