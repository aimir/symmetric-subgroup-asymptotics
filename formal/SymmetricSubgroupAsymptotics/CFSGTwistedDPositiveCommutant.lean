import SymmetricSubgroupAsymptotics.CFSGPairedSquareZeroCommutant
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSignedGroups
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation

/-! Commuting with the actual relative positive subgroup forces
commutation with every ambient positive simple-root direction. The
quadratic term of the paired terminal word is separated first, so
the argument remains valid in characteristic two and at q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveCommutant
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeSignedGroups
open CFSGTwistedDSingularPrefix CFSGSerreOrdinaryTwists

theorem terminal_directions (n : ℕ) (q : CFSG.PrimePower)
    (A : Mat (q.Extension 2) (n + 2))
    (hA : ∀ a : q.Extension 2,
      A * (pairedRoot n q false a : Mat (q.Extension 2) (n + 2)) =
        (pairedRoot n q false a : Mat (q.Extension 2) (n + 2)) * A) :
    A * positive (q.Extension 2) (n + 2) (pen n) =
        positive (q.Extension 2) (n + 2) (pen n) * A ∧
      A * positive (q.Extension 2) (n + 2) (last n) =
        positive (q.Extension 2) (n + 2) (last n) * A := by
  obtain ⟨θ, hθ⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  apply CFSGPairedSquareZeroCommutant.commute_of_paired_words
    (positive (q.Extension 2) (n + 2) (pen n))
    (positive (q.Extension 2) (n + 2) (last n)) A
    (by simpa only [pow_two] using positive_sq_zero (q.Extension 2) (n + 2) (pen n))
    (by simpa only [pow_two] using positive_sq_zero (q.Extension 2) (n + 2) (last n))
    (CFSGOrthogonalDTerminalRootCommutation.rootMatrix_commute (q.Extension 2) n false false).eq
    (definingFieldAutomorphism q 2) θ hθ
    (CFSGPairedSquareZeroCommutant.trace_pair_exists _ θ hθ)
  intro a
  exact hA a

theorem positive_directions (n : ℕ) (q : CFSG.PrimePower)
    (A : Mat (q.Extension 2) (n + 2))
    (hA : ∀ u ∈ signedRootGroup n q false,
      A * (u : Mat (q.Extension 2) (n + 2)) = (u : Mat (q.Extension 2) (n + 2)) * A) :
    ∀ i : Fin (n + 2), A * positive (q.Extension 2) (n + 2) i =
      positive (q.Extension 2) (n + 2) i * A := by
  have hp := terminal_directions n q A (fun a =>
    hA _ (Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)))
  intro i
  by_cases hil : i = last n
  · simpa only [hil] using hp.2
  by_cases hip : i = pen n
  · simpa only [hip] using hp.1
  have hiv : i.val < n := by
    have hb := i.isLt
    have hl : i.val ≠ n + 1 := fun h => hil (Fin.ext h)
    have hpen : i.val ≠ n := fun h => hip (Fin.ext h)
    omega
  let j : Fin n := ⟨i.val, hiv⟩
  have hj : chainNode n j = i := Fin.ext rfl
  have h := hA (rootTransvection (q.Extension 2) (n + 2) false (chainNode n j) 1)
    (Subgroup.subset_closure (Or.inl ⟨j, (1 : CFSGTwistedA2FixedField.fixedField q), rfl⟩))
  rw [hj] at h
  change A * (1 + (1 : q.Extension 2) • positive (q.Extension 2) (n + 2) i) =
    (1 + (1 : q.Extension 2) • positive (q.Extension 2) (n + 2) i) * A at h
  simp only [one_smul, mul_add, add_mul, mul_one, one_mul] at h
  exact add_left_cancel h

end SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveCommutant
