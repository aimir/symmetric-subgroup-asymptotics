import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationChainCommutators
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootLineTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices

/-! Once the actual short line and pure Weyl word have been recovered,
the two last-coordinate star lines propagate around the entire signed
coordinate cycle. No finiteness, field-size or rank-parity premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureStarCoverage
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDGenerationInitialElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationInitialRootMatrices
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDGenerationChainCommutators
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationSignedRootConjugation
open CFSGOrthogonalDGenerationSignedRootLineTransport
variable (K : Type) [Field K]

def StarPair (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ) (a : Index (s + 4)) : Prop :=
  HasRootLine H (rootArray K a (Sum.inl (last (s + 2)))) ∧
    HasRootLine H (rootArray K a (Sum.inr (last (s + 2))))

theorem starPair_conjugate (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hW : (coxeterWeyl K (s + 3)).val ∈ H) (a : Index (s + 4)) (ha : StarPair K s H a) :
    StarPair K s H (cyclePerm (s + 2) a) := by
  constructor
  · have h := coxeter_line_transfer K (s + 2) H hW _ _ ha.2
    change HasRootLine H (rootArray K (cyclePerm (s + 2) a)
      (cyclePerm (s + 2) (Sum.inr (Fin.last (s + 3))))) at h
    rw [cyclePerm_negative_last] at h
    exact h
  · have h := coxeter_line_transfer K (s + 2) H hW _ _ ha.1
    change HasRootLine H (rootArray K (cyclePerm (s + 2) a)
      (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 3))))) at h
    rw [cyclePerm_positive_last] at h
    exact h

theorem initial_star_pair (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hW : (coxeterWeyl K (s + 3)).val ∈ H)
    (hA : ∀ a, (initialShortRoot K s a).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2))))) :
    StarPair K s H (Sum.inl (0 : Fin (s + 4))) := by
  have hm : cyclePerm (s + 2) (Sum.inl (0 : Fin (s + 4))) = Sum.inl (second s) :=
    cyclePerm_shift (s + 2) false 0 (by omega)
  have hL : cyclePerm (s + 2) (Sum.inl (last (s + 2))) = Sum.inr (last (s + 2)) :=
    cyclePerm_positive_last (s + 2)
  have hN : cyclePerm (s + 2) (Sum.inr (last (s + 2))) = Sum.inl (last (s + 2)) :=
    cyclePerm_negative_last (s + 2)
  have h0 : HasRootLine H (chainArray (0 : Fin (s + 4)) (last (s + 2))) := by
    have h := inverse_coxeter_line_transfer K (s + 2) H hW (Sum.inl 0) (Sum.inl (last (s + 2)))
      (by simpa only [hm, hL] using hB)
    exact h
  have hα : HasRootLine H (chainArray (second s) (0 : Fin (s + 4))) := by
    intro a
    exact ⟨(initialShortRoot K s a).val, hA a, initialShortRoot_coe K s a⟩
  have h1 := chain_chain_lines H (second s) 0 (last (s + 2))
    (second_ne_zero s) (second_ne_last s) (Ne.symm (last_ne_zero s)) hα h0
  constructor
  · exact h0
  · apply inverse_coxeter_line_transfer K (s + 2) H hW (Sum.inl 0) (Sum.inr (last (s + 2)))
    simpa only [hm, hN] using h1

def column (s : ℕ) (side : Bool) (j : Fin (s + 3)) : Index (s + 4) :=
  if side then Sum.inr j.castSucc else Sum.inl j.castSucc

theorem all_stars (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hW : (coxeterWeyl K (s + 3)).val ∈ H)
    (h0 : StarPair K s H (Sum.inl (0 : Fin (s + 4)))) :
    ∀ (side : Bool) (j : Fin (s + 3)), StarPair K s H (column s side j) := by
  have hstep (side : Bool) (j : ℕ) (hj : j < s + 2)
      (h : StarPair K s H (column s side (⟨j, by omega⟩ : Fin (s + 3)))) :
      StarPair K s H (column s side (⟨j + 1, by omega⟩ : Fin (s + 3))) := by
    have hp := starPair_conjugate K s H hW _ h
    have he := cyclePerm_shift (s + 2) side j hj
    change cyclePerm (s + 2) (column s side (⟨j, by omega⟩ : Fin (s + 3))) =
      column s side (⟨j + 1, by omega⟩ : Fin (s + 3)) at he
    rw [he] at hp
    exact hp
  have hp : ∀ j : ℕ, ∀ hj : j < s + 3,
      StarPair K s H (column s false (⟨j, hj⟩ : Fin (s + 3))) := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih => intro hj; exact hstep false j (by omega) (ih (by omega))
  have hn0 : StarPair K s H (column s true (0 : Fin (s + 3))) := by
    have h := starPair_conjugate K s H hW _ (hp (s + 2) (by omega))
    change StarPair K s H (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 2)).castSucc)) at h
    rw [cyclePerm_positive_penultimate] at h
    exact h
  have hn : ∀ j : ℕ, ∀ hj : j < s + 3,
      StarPair K s H (column s true (⟨j, hj⟩ : Fin (s + 3))) := by
    intro j
    induction j with
    | zero => intro _; exact hn0
    | succ j ih => intro hj; exact hstep true j (by omega) (ih (by omega))
  intro side j
  cases side
  · exact hp j.val j.isLt
  · exact hn j.val j.isLt

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureStarCoverage
