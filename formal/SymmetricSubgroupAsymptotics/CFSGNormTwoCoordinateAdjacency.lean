import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! Pure root-lattice adjacency: the exact geometric neighbor facts used
by later source-kernel proofs, independent of any matrix group or
normal-root-generation proof. Proofs are extracted verbatim from the
checked coordinate group leaves, with the same original Cartan data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjacency
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

include hd hs hp ho

theorem offdiagonal_nonzero_eq_neg_one (i j : Fin r) (hij : i≠j) (hA : A i j≠0) : A i j= -1 := by
  have hne : (s₀ i : Roots A)≠(s₀ j : Roots A) := by
    intro he
    exact hij ((s₀).injective (Subtype.ext he))
  have hopp : (s₀ i : Roots A).val≠ -(s₀ j : Roots A).val := by
    intro he
    have hx := congrFun he i
    change (Pi.single i (1:ℤ) : Fin r→ℤ) i= -(Pi.single j (1:ℤ) : Fin r→ℤ) i at hx
    simp [Pi.single_apply,hij,Ne.symm hij] at hx
  have hi := root_pairing_interior A hs hp (s₀ i) (s₀ j) hne hopp
  have hentry : integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val=A i j := by
    change Matrix.toBilin' A (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))=A i j
    exact Matrix.toBilin'_single A i j
  rw [hentry] at hi
  have hn := ho i j hij
  omega


theorem exists_adjacent_to [Nontrivial (Fin r)] (i : Fin r) :
    ∃ j : Fin r, i ≠ j ∧ A i j = -1 := by
  obtain ⟨a, ha⟩ := exists_ne i
  by_contra hn
  push Not at hn
  have hall : ∀ a : Fin r, a = i := by
    intro a
    apply CFSGNormTwoCoordinateDominantSupport.coordinate_cartan_induction
      A hd hs hp ho (fun b => b = i) i a rfl
    intro b c hb hcb
    subst b
    by_contra hci
    have hcA := offdiagonal_nonzero_eq_neg_one
      A hd hs hp ho c i hci hcb
    have hiA : A i c = -1 := (congrFun (congrFun hs c) i).trans hcA
    exact hn c (Ne.symm hci) hiA
  exact ha (hall a)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjacency
