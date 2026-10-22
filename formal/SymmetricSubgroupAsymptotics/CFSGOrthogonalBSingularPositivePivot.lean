import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTerminalVectorAction
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity

/-! Every original nonzero singular B-vector has a positive pivot after
an actual root-group word. The negative-only case uses determinant-one
SL normalization followed by the original terminal B Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
open CFSGOrthogonalBGenerationTerminalWeyl
variable (K : Type) [Field K]

theorem exists_positive_pivot (s : ℕ) (v : Index (s + 2) → K) (hv : v ≠ 0)
    (hs : (gram K (s + 2)).toBilin' v v = 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      positivePart K (s + 2) ((g.val : Mat K (s + 2)) *ᵥ v) ≠ 0 := by
  obtain hx | hy := positive_or_negative_nonzero K (s + 2) v hv hs
  · refine ⟨1, ?_⟩
    simpa only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] using hx
  · have hlast : (Fin.last (s + 1) : Fin (s + 2)) ≠ 0 := by
      intro h
      have he := congrArg Fin.val h
      change s + 1 = 0 at he
      omega
    obtain ⟨B, hB⟩ := CFSGTypeAVectorTransitivity.exists_normalize
      (Fin.last (s + 1)) 0 hlast (negativePart K (s + 2) v) hy
    change B.val *ᵥ negativePart K (s + 2) v = Pi.single (Fin.last (s + 1)) 1 at hB
    let A : NaturalSL K (s + 2) := B.transpose⁻¹
    let d : elementaryRootGroup K (s + 2) := doubleIntoElementary K (s + 2) A
    have hd : negativePart K (s + 2) ((d.val : Mat K (s + 2)) *ᵥ v) =
        Pi.single (Fin.last (s + 1)) 1 := by
      change negativePart K (s + 2) (((doubleIntoElementary K (s + 2) A).val : Mat K (s + 2)) *ᵥ v) = _
      rw [double_negativePart]
      change (B.transpose⁻¹⁻¹).val.transpose *ᵥ negativePart K (s + 2) v = _
      rw [inv_inv, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose]
      exact hB
    let g : elementaryRootGroup K (s + 2) := terminalWeyl K (s + 1) * d
    have hg : (((g.val : Mat K (s + 2)) *ᵥ v) (pos (s + 2) (Fin.last (s + 1)))) = -1 := by
      change ((((terminalWeyl K (s + 1)).val : Mat K (s + 2)) * (d.val : Mat K (s + 2))) *ᵥ v)
        (pos (s + 2) (Fin.last (s + 1))) = -1
      rw [← Matrix.mulVec_mulVec, terminalWeyl_positive_last]
      have hh : ((d.val : Mat K (s + 2)) *ᵥ v) (neg (s + 2) (Fin.last (s + 1))) = 1 := by
        simpa only [negativePart, Pi.single_eq_same] using congrFun hd (Fin.last (s + 1))
      rw [hh]
    refine ⟨g, ?_⟩
    intro hz
    have hh := congrFun hz (Fin.last (s + 1))
    change (((g.val : Mat K (s + 2)) *ᵥ v) (pos (s + 2) (Fin.last (s + 1)))) = 0 at hh
    rw [hg] at hh
    exact neg_ne_zero.mpr one_ne_zero hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
