import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates

/-! Every nonzero original D vector has a positive pivot after an
actual elementary word. A negative-only vector is normalized by the
original SL double action and the actual terminal fork Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDBinaryElements CFSGOrthogonalDGenerationForkTorus
variable (K : Type) [Field K]

theorem positive_or_negative_nonzero (r : ℕ) (v : Index r → K) (hv : v ≠ 0) :
    positivePart K r v ≠ 0 ∨ negativePart K r v ≠ 0 := by
  by_cases hp : positivePart K r v = 0
  · right
    intro hn
    apply hv
    funext i
    cases i with
    | inl j => exact congrFun hp j
    | inr j => exact congrFun hn j
  · exact Or.inl hp

theorem exists_positive_pivot (s : ℕ) (v : Index (s + 2) → K) (hv : v ≠ 0) :
    ∃ g : elementaryRootGroup K (s + 2),
      positivePart K (s + 2) ((g.val : Mat K (s + 2)) *ᵥ v) ≠ 0 := by
  obtain hx | hy := positive_or_negative_nonzero K (s + 2) v hv
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
    let g : elementaryRootGroup K (s + 2) := simpleWeyl K (s + 2) (last s) * d
    have hg : (((g.val : Mat K (s + 2)) *ᵥ v) (Sum.inl (pen s))) = -1 := by
      change ((((simpleWeyl K (s + 2) (last s)).val : Mat K (s + 2)) *
        (d.val : Mat K (s + 2))) *ᵥ v) (Sum.inl (pen s)) = -1
      rw [← Matrix.mulVec_mulVec, fork_positive_penultimate]
      have hh : ((d.val : Mat K (s + 2)) *ᵥ v) (Sum.inr (last s)) = 1 := by
        simpa only [negativePart, Pi.single_eq_same] using congrFun hd (Fin.last (s + 1))
      rw [hh]
    refine ⟨g, ?_⟩
    intro hz
    have hh := congrFun hz (pen s)
    change (((g.val : Mat K (s + 2)) *ᵥ v) (Sum.inl (pen s))) = 0 at hh
    rw [hg] at hh
    exact neg_ne_zero.mpr one_ne_zero hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexVectorCoordinates
