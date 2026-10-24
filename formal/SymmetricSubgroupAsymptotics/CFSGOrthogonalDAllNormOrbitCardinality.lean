import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllNormVectorOrbit
import SymmetricSubgroupAsymptotics.HyperbolicNormLevelSliceCardinality

/-! Every nonzero split-D natural-vector orbit contains an entire
positive-nonzero norm slice. The bound applies at every norm, in every
characteristic, and uses actual elementary words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllNormOrbitCardinality

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDAllNormVectorOrbit HyperbolicNormLevelSliceCardinality
open CFSGParabolicQuadricCount
variable (K : Type) [Field K]

def vectorOrbit (s : ℕ) (v : Index (s + 2) → K) : Set (Index (s + 2) → K) :=
  {w | ∃ g : elementaryRootGroup K (s + 2), (g.val : Mat K (s + 2)) *ᵥ v = w}

theorem norm_slice_le_vectorOrbit [Finite K] (s : ℕ)
    (v : Index (s + 2) → K) (hv : v ≠ 0) :
    (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 1) ≤
      Nat.card (vectorOrbit K s v) := by
  let Q : PUnit → K := fun _ => 0
  let S := LevelSlice (I := Fin (s + 2)) Q (splitQ K v)
  let e : S → vectorOrbit K s v := fun p => by
    let w : Index (s + 2) → K := Sum.elim p.val.1.1 p.val.2
    have hw : w ≠ 0 := by
      intro hz
      apply p.property.1
      funext i
      exact congrFun hz (Sum.inl i)
    have hQ : splitQ K w = splitQ K v := by
      change dotDual p.val.1.1 p.val.2 = splitQ K v
      simpa only [Q, add_zero] using p.property.2
    refine ⟨w, ?_⟩
    obtain ⟨g, hg⟩ := exists_map_of_same_norm K s v w hv hw hQ.symm
    exact ⟨g, hg⟩
  have he : Function.Injective e := by
    intro p t h
    have hv := congrArg (fun w : vectorOrbit K s v => w.val) h
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · funext i
        exact congrFun hv (Sum.inl i)
      · exact Subsingleton.elim _ _
    · funext i
      exact congrFun hv (Sum.inr i)
  have hc : Nat.card S =
      (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 1) := by
    have h := card_levelSlice (I := Fin (s + 2)) Q (splitQ K v)
    have hs : s + 2 - 1 = s + 1 := by omega
    simpa only [Fintype.card_fin, Nat.card_unique, mul_one, hs] using h
  rw [← hc]
  exact Nat.card_le_card_of_injective e he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllNormOrbitCardinality
