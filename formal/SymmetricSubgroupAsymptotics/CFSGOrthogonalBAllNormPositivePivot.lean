import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPositivePivot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership

/-! Every nonzero original B natural vector admits a positive pivot.
The actual negative-block normalization and terminal Weyl word work at
every norm; a literal short root also handles a pure middle vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormPositivePivot

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBGenerationSLChain CFSGOrthogonalBGenerationTerminalWeyl
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortMembership
variable (K : Type) [Field K]

theorem exists_positive_pivot_of_negative (s : ℕ) (v : Index (s + 2) → K)
    (hy : negativePart K (s + 2) v ≠ 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      positivePart K (s + 2) ((g.val : Mat K (s + 2)) *ᵥ v) ≠ 0 := by
  have hlast : (Fin.last (s + 1) : Fin (s + 2)) ≠ 0 := by
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
    change negativePart K (s + 2)
      (((doubleIntoElementary K (s + 2) A).val : Mat K (s + 2)) *ᵥ v) = _
    rw [double_negativePart]
    change (B.transpose⁻¹⁻¹).val.transpose *ᵥ negativePart K (s + 2) v = _
    rw [inv_inv, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose]
    exact hB
  let g : elementaryRootGroup K (s + 2) := terminalWeyl K (s + 1) * d
  have hg : (((g.val : Mat K (s + 2)) *ᵥ v) (pos (s + 2) (Fin.last (s + 1)))) = -1 := by
    change ((((terminalWeyl K (s + 1)).val : Mat K (s + 2)) *
      (d.val : Mat K (s + 2))) *ᵥ v) (pos (s + 2) (Fin.last (s + 1))) = -1
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

theorem exists_positive_pivot (s : ℕ) (v : Index (s + 2) → K) (hv : v ≠ 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      positivePart K (s + 2) ((g.val : Mat K (s + 2)) *ᵥ v) ≠ 0 := by
  by_cases hx : positivePart K (s + 2) v = 0
  · by_cases hy : negativePart K (s + 2) v = 0
    · have hm : v (middle (s + 2)) ≠ 0 := by
        intro hz
        apply hv
        funext i
        rcases i with (i | i) | ⟨⟩
        · exact congrFun hx i
        · exact congrFun hy i
        · exact hz
      let g : elementaryRootGroup K (s + 2) :=
        ⟨shortUnit K (s + 2) (Sum.inl 0) 1,
          shortUnit_mem K (s + 1) (Sum.inl 0) 1⟩
      have hpos : v (pos (s + 2) 0) = 0 := congrFun hx 0
      have hneg : v (neg (s + 2) 0) = 0 := congrFun hy 0
      have hg : ((g.val : Mat K (s + 2)) *ᵥ v) (pos (s + 2) 0) =
          v (middle (s + 2)) := by
        change ((shortUnit K (s + 2) (Sum.inl 0) 1 : Mat K (s + 2)) *ᵥ v)
          (pos (s + 2) 0) = _
        rw [CFSGOrthogonalBVectorCoordinates.shortUnit_vector_action]
        simp [pos, middle, paired, hpos, hneg, Pi.single_apply]
      refine ⟨g, ?_⟩
      intro hz
      have h := congrFun hz 0
      change ((g.val : Mat K (s + 2)) *ᵥ v) (pos (s + 2) 0) = 0 at h
      exact hm (hg.symm.trans h)
    · exact exists_positive_pivot_of_negative K s v hy
  · refine ⟨1, ?_⟩
    simpa only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] using hx

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormPositivePivot
