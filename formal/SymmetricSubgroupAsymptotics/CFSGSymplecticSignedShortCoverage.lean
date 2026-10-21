import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterChainCrossing
import SymmetricSubgroupAsymptotics.CFSGActualMatrixRootLines

/-! Complete same-side short-root coverage over every field. Full
parameter lines absorb the genuine signed terminal crossing; no
characteristic-two simplification occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines

theorem signed_chain_side_coverage (K : Type) [Field K] (s : ℕ)
    (H : Subgroup ((Mat K (s + 2))ˣ)) (hW : (coxeterWeyl K (s + 1)).val ∈ H)
    (side : Bool) (h0 : HasRootLine H (signedChainRoot K (s + 1) side (0 : Fin (s + 1)))) :
    ∀ i : Fin (s + 1), HasRootLine H (signedChainRoot K (s + 1) side i) := by
  have aux : ∀ k : ℕ, ∀ hk : k < s + 1,
      HasRootLine H (signedChainRoot K (s + 1) side (⟨k, hk⟩ : Fin (s + 1))) := by
    intro k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih =>
      intro hk
      have hstep := coxeter_signedChainRoot_shift K (s + 1) side
        (⟨k, by omega⟩ : Fin (s + 1)) (by change k + 1 < s + 1; omega)
      exact hasRootLine_conjugate H (coxeterWeyl K (s + 1)).val hW _ _ 1 one_ne_zero
        (by simpa only [one_smul] using hstep) (ih (Nat.lt_of_succ_lt hk))
  intro i
  exact aux i.val i.isLt

theorem signed_short_coverage (K : Type) [Field K] (s : ℕ)
    (H : Subgroup ((Mat K (s + 2))ˣ)) (hW : (coxeterWeyl K (s + 1)).val ∈ H)
    (h0 : HasRootLine H (signedChainRoot K (s + 1) false (0 : Fin (s + 1)))) :
    ∀ side : Bool, ∀ i : Fin (s + 1), HasRootLine H (signedChainRoot K (s + 1) side i) := by
  have hpos := signed_chain_side_coverage K s H hW false h0
  have hlast := hpos (Fin.last s)
  have htwo : (coxeterWeyl K (s + 1)).val * (coxeterWeyl K (s + 1)).val ∈ H :=
    H.mul_mem hW hW
  have hcross :
      (((coxeterWeyl K (s + 1)).val * (coxeterWeyl K (s + 1)).val : (Mat K (s + 2))ˣ) :
        Mat K (s + 2)) * signedChainRoot K (s + 1) false (Fin.last s) *
        (↑(((coxeterWeyl K (s + 1)).val * (coxeterWeyl K (s + 1)).val)⁻¹) : Mat K (s + 2)) =
      signedChainRoot K (s + 1) true (0 : Fin (s + 1)) := by
    change (((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) *
      ((coxeterWeyl K (s + 1)).val : Mat K (s + 2))) * _ *
      ((↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) *
        (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2))) = _
    simpa only [mul_assoc] using coxeter_chain_crossing K s
  have hneg0 := hasRootLine_conjugate H
    ((coxeterWeyl K (s + 1)).val * (coxeterWeyl K (s + 1)).val) htwo _ _ 1 one_ne_zero
    (by simpa only [one_smul] using hcross) hlast
  have hneg := signed_chain_side_coverage K s H hW true hneg0
  intro side
  cases side
  · exact hpos
  · exact hneg

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
