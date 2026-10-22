import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4DualPolarStep
import Mathlib.Logic.Relation

/-! Genuine connectedness of the maximal-singular dual-polar graph.
The proof increases the target intersection one dimension at a time;
actual quadratic zero is retained in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
open CFSGOrthogonalDIndexQuadraticNeighborPlane
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def MaximalSingular (Q : QuadraticForm K V) (r : ℕ) :=
  {P : Submodule K V // Module.finrank K P = r ∧ ∀ x ∈ P, Q x = 0}

def DualAdjacent (Q : QuadraticForm K V) (r : ℕ) (P L : MaximalSingular Q r) : Prop :=
  P ≠ L ∧ Module.finrank K ↥(P.val ⊓ L.val) + 1 = r

theorem maximalSingular_self_orthogonal (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P : MaximalSingular Q r) :
    LinearMap.BilinForm.orthogonal Q.polarBilin P.val = P.val := by
  have hle : P.val ≤ LinearMap.BilinForm.orthogonal Q.polarBilin P.val := by
    intro x hx y hy
    exact polar_zero_of_singular Q P.val P.property.2 y x hy hx
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ, hV, P.property.1]
  omega

theorem dual_polar_graph_connected (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P L : MaximalSingular Q r) : Relation.ReflTransGen (DualAdjacent Q r) P L := by
  suffices hall : ∀ n, ∀ P : MaximalSingular Q r,
      r - Module.finrank K ↥(P.val ⊓ L.val) = n →
        Relation.ReflTransGen (DualAdjacent Q r) P L by
    exact hall _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn
    by_cases he : P = L
    · subst P
      exact Relation.ReflTransGen.refl
    · have hnot : ¬ L.val ≤ P.val := by
        intro h
        have hh : L.val = P.val := Submodule.eq_of_le_of_finrank_le h
          (by rw [P.property.1, L.property.1])
        exact he (Subtype.ext hh.symm)
      obtain ⟨u, huL, huP⟩ := Set.not_subset.mp hnot
      obtain ⟨R, hRP, hdR, hzR, hcap, hgain⟩ := dual_polar_replacement_step Q P.val L.val r
        P.property.1 (maximalSingular_self_orthogonal Q hQ r hV P)
        P.property.2 L.property.2 u huL huP
      let R' : MaximalSingular Q r := ⟨R, hdR, hzR⟩
      have hadj : DualAdjacent Q r P R' :=
        ⟨fun hh => hRP (congrArg Subtype.val hh).symm, hcap⟩
      have hhi := Submodule.finrank_mono (inf_le_left : R ⊓ L.val ≤ R)
      rw [hdR] at hhi
      have hlt : r - Module.finrank K ↥(R ⊓ L.val) < n := by
        rw [← hn]
        omega
      exact (Relation.ReflTransGen.single hadj).trans
        (ih _ hlt R' rfl)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
