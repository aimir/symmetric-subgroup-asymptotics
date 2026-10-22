import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalCommutant
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual natural A-image kernel

The literal elementary matrices and original Serre group act on the same
integral tensor image. The elementary action kills exactly its actual
centre. This is unconditional in the characteristic and does not presume
faithfulness of the original Serre source or a unitary identification.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

abbrev NaturalElementary (K : Type) [Field K] (r : ℕ) :=
  CFSGSerreSquareZeroMatrix.elementaryGroup K (naturalRootUnit K r)

theorem naturalBaseChange_E (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K
      (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.A r)
        (CartanMatrix.Generators.E i)) = positive K r i := by
  rw [CFSGSerreSquareZeroMatrix.baseChange_generator]
  exact map_positive ℤ r (Int.castRingHom K) i

theorem naturalBaseChange_F (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K
      (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.A r)
        (CartanMatrix.Generators.F i)) = negative K r i := by
  rw [CFSGSerreSquareZeroMatrix.baseChange_generator]
  exact map_negative ℤ r (Int.castRingHom K) i

theorem naturalImage_centralizer (K : Type) [Field K] (r : ℕ) (hr : 1 ≤ r)
    (M : Mat K r)
    (hM : ∀ x : Space (CartanMatrix.A r) K,
      M * CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x =
        CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x * M) :
    ∃ c : K, M = c • (1 : Mat K r) := by
  apply natural_commutant_scalar K r hr M
  intro neg i
  cases neg
  · have h := hM (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.A r)
      (CartanMatrix.Generators.E i))
    simpa only [naturalBaseChange_E, rootMatrix, Bool.false_eq_true, if_false] using h
  · have h := hM (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.A r)
      (CartanMatrix.Generators.F i))
    simpa only [naturalBaseChange_F, rootMatrix, if_true] using h

theorem naturalElementary_center_iff_scalar (K : Type) [Field K] (r : ℕ)
    (hr : 1 ≤ r) (u : NaturalElementary K r) :
    u ∈ Subgroup.center (NaturalElementary K r) ↔
      ∃ c : K, (u.val : Mat K r) = c • (1 : Mat K r) := by
  constructor
  · intro hu
    apply natural_commutant_scalar K r hr (u.val : Mat K r)
    intro neg i
    let v : NaturalElementary K r := CFSGSerreSquareZeroMatrix.elementaryRoot K
      (naturalRootUnit K r) neg i 1
    have h := congrArg (fun w : NaturalElementary K r => (w.val : Mat K r))
      ((Subgroup.mem_center_iff.mp hu) v).symm
    change (u.val : Mat K r) * (1 + 1 • rootMatrix K r neg i) =
      (1 + 1 • rootMatrix K r neg i) * (u.val : Mat K r) at h
    simp only [one_smul, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  · rintro ⟨c, hc⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply Units.ext
    change (v.val : Mat K r) * (u.val : Mat K r) =
      (u.val : Mat K r) * (v.val : Mat K r)
    rw [hc]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem naturalElementaryAction_ker (K : Type) [Field K] (r : ℕ) (hr : 1 ≤ r) :
    (naturalElementaryAction K r).ker = Subgroup.center (NaturalElementary K r) := by
  ext u
  change naturalElementaryAction K r u = 1 ↔
    u ∈ Subgroup.center (NaturalElementary K r)
  constructor
  · intro hu
    apply (naturalElementary_center_iff_scalar K r hr u).mpr
    apply naturalImage_centralizer K r hr (u.val : Mat K r)
    intro x
    have h := DFunLike.congr_fun hu
      ((CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K).rangeRestrict x)
    have he := congrArg Subtype.val h
    change (u.val : Mat K r) *
      CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x *
        (↑(u.val⁻¹) : Mat K r) =
      CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x at he
    exact (CFSGUnitConjugation.fix_iff_commute u.val _).mp he
  · intro hu
    obtain ⟨c, hc⟩ := (naturalElementary_center_iff_scalar K r hr u).mp hu
    apply LinearEquiv.ext
    intro y
    apply Subtype.ext
    change (u.val : Mat K r) * y.val * (↑(u.val⁻¹) : Mat K r) = y.val
    apply (CFSGUnitConjugation.fix_iff_commute u.val _).mpr
    rw [hc]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

def naturalElementaryProjectiveActionEquiv (K : Type) [Field K] (r : ℕ)
    (hr : 1 ≤ r) :
    (NaturalElementary K r ⧸ Subgroup.center (NaturalElementary K r)) ≃*
      (naturalElementaryAction K r).range := by
  let f := naturalElementaryAction K r
  have hf : f.ker = Subgroup.center (NaturalElementary K r) :=
    naturalElementaryAction_ker K r hr
  letI : f.ker.Normal := f.normal_ker
  exact (QuotientGroup.quotientMulEquivOfEq hf.symm).trans
    (QuotientGroup.quotientKerEquivRange f)

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
