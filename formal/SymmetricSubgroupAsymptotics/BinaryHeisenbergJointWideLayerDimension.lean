import SymmetricSubgroupAsymptotics.BinaryPairHighLayerDistinctness
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel13
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14

/-! A selected fifteen-state compatibility receipt bounds the JOINT
original inner kernel and outer pair-layer dimensions by fourteen.
Only the three actual high-head states occur in the two outer layers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads

private def highIndex (s : Fin 3) : Fin 15 := ⟨12 + s.val, by omega⟩
private def basisProductCompatible (k s l : Fin 15) : Prop :=
  ∀ a : Fin (charts k).1, ∀ b : Fin (charts s).1,
    (charts k).2.inclusion (Pi.single a 1) *
      (charts s).2.inclusion (Pi.single b 1) ∈ (charts l).2.space

/-- Only the two already certified borderline kernels can survive the
strict joint-dimension threshold with different high-head layers. -/
private theorem high_dimension_cover : ∀ (k : Fin 15) (s l : Fin 3),
    basisProductCompatible k (highIndex s) (highIndex l) →
    14 < (charts k).1 + (charts (highIndex s)).1 + (charts (highIndex l)).1 →
    s = l ∨ k = 13 ∨ k = 14 := by
  unfold basisProductCompatible
  decide +kernel

private theorem all_head_le_two (A : Subrepresentation rho) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2 := by
  obtain ⟨i, rfl⟩ := complete A
  exact (coinvariants_finrank_le i).trans (by
    have h : ∀ i : Fin 15, headCeiling i ≤ 2 := by decide
    exact h i)

private theorem high_state (A : Subrepresentation rho)
    (hA : 2 ≤ Module.finrank (ZMod 2) A.toRepresentation.Coinvariants) :
    ∃ s : Fin 3, states (highIndex s) = A := by
  rcases head_gt_one_states A (by omega) with h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

theorem head_four_joint_layer_dimension_le_fourteen
    (K S L : Subrepresentation rho) (hconstant : (1 : V) ∈ K.toSubmodule)
    (hproduct : binaryCoordinateProductSpan K.toSubmodule S.toSubmodule ≤ L.toSubmodule)
    (hhead : 4 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K.toSubmodule S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation))) :
    Module.finrank (ZMod 2) K.toSubmodule + Module.finrank (ZMod 2) S.toSubmodule +
      Module.finrank (ZMod 2) L.toSubmodule ≤ 14 := by
  obtain ⟨hs, hl, hne⟩ := binary_head_four_pair_layer_profile rho K.toSubmodule hconstant S L
    (all_head_le_two S) (all_head_le_two L) hhead
  obtain ⟨k, rfl⟩ := complete K
  obtain ⟨s, rfl⟩ := high_state S hs
  obtain ⟨l, rfl⟩ := high_state L hl
  have hc : basisProductCompatible k (highIndex s) (highIndex l) := by
    intro a b
    have ha : (charts k).2.inclusion (Pi.single a 1) ∈ (states k).toSubmodule := by
      rw [states_space]
      exact ⟨_, rfl⟩
    have hb : (charts (highIndex s)).2.inclusion (Pi.single b 1) ∈
        (states (highIndex s)).toSubmodule := by
      rw [states_space]
      exact ⟨_, rfl⟩
    exact hproduct (binaryCoordinateProductSpan.product_mem _ _ _ ha _ hb)
  by_contra hbad
  have hd : 14 < (charts k).1 + (charts (highIndex s)).1 + (charts (highIndex l)).1 := by
    simpa only [states_space, BinaryCoordinateSpace.finrank] using Nat.lt_of_not_ge hbad
  rcases high_dimension_cover k s l hc hd with heq | hk | hk
  · subst l
    exact hne rfl
  · subst k
    have hb := BinaryPairLayerHead8T22Kernel13.pair_bound _ _ hproduct
    exact (by decide : ¬ (4 ≤ (3 : ℕ))) (hhead.trans hb)
  · subst k
    obtain ⟨hS, hL⟩ := BinaryPairLayerHead8T22Kernel14.four_le_pair_head_forces_layers
      _ _ hproduct hhead
    have hsd : (charts (highIndex s)).1 = 3 := by
      have h := congrArg (fun A : Subrepresentation rho => Module.finrank (ZMod 2) A.toSubmodule) hS
      simpa only [states_space, BinaryCoordinateSpace.finrank] using h
    have hld : (charts (highIndex l)).1 = 7 := by
      have h := congrArg (fun A : Subrepresentation rho => Module.finrank (ZMod 2) A.toSubmodule) hL
      simpa only [states_space, BinaryCoordinateSpace.finrank] using h
    have hkd : (charts (14 : Fin 15)).1 = 3 := by decide
    omega

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
