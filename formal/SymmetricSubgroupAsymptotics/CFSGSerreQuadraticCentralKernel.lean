import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A kernel element of the action on the SAME original tensor image
commutes with every original root generator. If the second coefficients
also commute, the actual elementary root generators force centrality.
The concrete norm-two application proves the latter condition integrally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCentralKernel
open CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (K : Type) [Field K]
    (hfour : ∀ neg i (x : CFSG.Models.Chevalley.Space A K),
      fieldSecond D K neg i * baseChange D K x * fieldSecond D K neg i = 0)

theorem kernel_commutes_root (g : canonicalElementaryGroup D K)
    (hg : g ∈ (canonicalImageAction D K hfour).ker) (neg : Bool) (i : Fin n) :
    Commute (g.val : Matrix I I K) (fieldRoot D K neg i) := by
  let y : (baseChange D K).range := (baseChange D K).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator A
      (CFSGSerreSquareZeroMatrix.rootGenerator neg i))
  have hy : y.val = fieldRoot D K neg i := by
    change baseChange D K (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator A
      (CFSGSerreSquareZeroMatrix.rootGenerator neg i)) = _
    rw [baseChange_generator]
    rfl
  have he := DFunLike.congr_fun hg y
  have hh := congrArg Subtype.val he
  change (g.val : Matrix I I K) * y.val * (↑(g.val⁻¹) : Matrix I I K) = y.val at hh
  rw [hy] at hh
  have hm := congrArg (fun M : Matrix I I K => M * (g.val : Matrix I I K)) hh
  simpa only [mul_assoc, Units.inv_mul, mul_one] using hm

theorem kernel_le_center_of_second
    (hsecond : ∀ g : canonicalElementaryGroup D K,
      g ∈ (canonicalImageAction D K hfour).ker → ∀ neg i,
        Commute (g.val : Matrix I I K) (fieldSecond D K neg i)) :
    (canonicalImageAction D K hfour).ker ≤ Subgroup.center (canonicalElementaryGroup D K) := by
  intro g hg
  rw [Subgroup.center_eq_iInf
    (elementaryRootSet_generate K (canonicalRoot D K))]
  simp only [Subgroup.mem_iInf]
  rintro x ⟨neg, i, t, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  apply Units.ext
  change (g.val : Matrix I I K) * (canonicalRoot D K neg i t : Matrix I I K) =
    (canonicalRoot D K neg i t : Matrix I I K) * (g.val : Matrix I I K)
  rw [canonicalRoot_val]
  have hX := kernel_commutes_root D K hfour g hg neg i
  have hY := hsecond g hg neg i
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, hX.eq, hY.eq]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCentralKernel
