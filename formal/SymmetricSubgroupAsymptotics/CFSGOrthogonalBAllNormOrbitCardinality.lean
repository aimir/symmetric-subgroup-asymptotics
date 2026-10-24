import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
import SymmetricSubgroupAsymptotics.HyperbolicNormLevelSliceCardinality

/-! Every nonzero odd-B natural-vector orbit contains a whole norm
slice with nonzero positive block. The actual original coordinate
equivalence retains its factor four; no field-size census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormOrbitCardinality

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOddQuadraticForm
open CFSGOrthogonalBAllNormVectorOrbit CFSGOrthogonalBSingularVectorCount
open HyperbolicNormLevelSliceCardinality CFSGParabolicQuadricCount
variable (K : Type) [Field K]

def vectorOrbit (s : ℕ) (v : Index (s + 2) → K) : Set (Index (s + 2) → K) :=
  {w | ∃ g : elementaryRootGroup K (s + 2), (g.val : Mat K (s + 2)) *ᵥ v = w}

private def coordinateNorm (s : ℕ)
    (p : (Fin (s + 2) → K) × (K × (Fin (s + 2) → K))) : K :=
  dotDual p.1 p.2.2 + p.2.1 ^ 2

theorem norm_slice_le_vectorOrbit [Finite K] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 2) → K) (hv : v ≠ 0) :
    (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 2) ≤
      Nat.card (vectorOrbit K s v) := by
  have h4 : (4 : K) ≠ 0 := by
    have he : (4 : K) = 2 * 2 := by ring
    rw [he]
    exact mul_ne_zero h2 h2
  let E := coordinates K (s + 2) h4
  let Q : K → K := fun a => a ^ 2
  let S := LevelSlice (I := Fin (s + 2)) Q ((gram K (s + 2)).toBilin' v v)
  let e : S → vectorOrbit K s v := fun p => by
    let w := E.symm (p.val.1.1, (p.val.1.2, p.val.2))
    have hw : w ≠ 0 := by
      intro hz
      have he := congrArg E hz
      change E (E.symm (p.val.1.1, (p.val.1.2, p.val.2))) = E 0 at he
      rw [E.apply_symm_apply] at he
      have hzero : (E 0).1 = 0 := by
        funext i
        change (4 : K) * 0 = 0
        exact mul_zero _
      exact p.property.1 ((congrArg Prod.fst he).trans hzero)
    have hGram : (gram K (s + 2)).toBilin' w w =
        (gram K (s + 2)).toBilin' v v := by
      rw [gram_norm_dot]
      change coordinateNorm K s (E w) = _
      change coordinateNorm K s (E (E.symm (p.val.1.1, (p.val.1.2, p.val.2)))) = _
      rw [E.apply_symm_apply]
      exact p.property.2
    have hQ : quadratic K (s + 2) w = quadratic K (s + 2) v := by
      rw [quadratic_apply, quadratic_apply, hGram]
    refine ⟨w, ?_⟩
    obtain ⟨g, hg⟩ := exists_map_of_same_norm K h2 s v w hv hw hQ.symm
    exact ⟨g, hg⟩
  have he : Function.Injective e := by
    intro p t h
    have hv := congrArg (fun w : vectorOrbit K s v => w.val) h
    have hc := congrArg E hv
    change E (E.symm (p.val.1.1, (p.val.1.2, p.val.2))) =
      E (E.symm (t.val.1.1, (t.val.1.2, t.val.2))) at hc
    rw [E.apply_symm_apply, E.apply_symm_apply] at hc
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun q : (Fin (s + 2) → K) × (K × (Fin (s + 2) → K)) => q.1) hc
      · exact congrArg (fun q : (Fin (s + 2) → K) × (K × (Fin (s + 2) → K)) => q.2.1) hc
    · exact congrArg (fun q : (Fin (s + 2) → K) × (K × (Fin (s + 2) → K)) => q.2.2) hc
  have hc : Nat.card S =
      (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 2) := by
    have h := card_levelSlice (I := Fin (s + 2)) Q ((gram K (s + 2)).toBilin' v v)
    have hs : s + 2 - 1 = s + 1 := by omega
    calc
      Nat.card S = (Nat.card K ^ (s + 2) - 1) * Nat.card K * Nat.card K ^ (s + 1) := by
        simpa only [Fintype.card_fin, hs] using h
      _ = (Nat.card K ^ (s + 2) - 1) * (Nat.card K ^ (s + 1) * Nat.card K) := by ac_rfl
      _ = _ := by rw [← pow_succ]
  rw [← hc]
  exact Nat.card_le_card_of_injective e he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBAllNormOrbitCardinality
