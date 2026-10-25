import SymmetricSubgroupAsymptotics.CFSGQuadraticNormFibreCardinality
import SymmetricSubgroupAsymptotics.FiniteDiagonalNormShellRecurrence

/-! Fixed-field norm counts and the matrix-valued Hermitian self-norm
have the SAME literal norm-one shells. Injectivity of the actual fixed
field embedding transfers the proved recurrence without a new count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticDiagonalNormShell
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField CFSGTwistedANaturalMatrices
open CFSGQuadraticNormFibreCardinality FiniteDiagonalNormShellRecurrence

theorem raw_shell_card_eq (q : CFSG.PrimePower) (n : ℕ) :
    shellCard (fun a : q.Extension 2 => definingFieldAutomorphism q 2 a*a) n=
      shellCard (normMap q) n := by
  classical
  have hsum (v : Fin n → q.Extension 2) :
      (fixedField q).subtype (∑ i, normMap q (v i))=
        ∑ i, definingFieldAutomorphism q 2 (v i)*v i := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change v i*definingFieldAutomorphism q 2 (v i)=definingFieldAutomorphism q 2 (v i)*v i
    exact mul_comm _ _
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro v
  rw [←hsum]
  change (fixedField q).subtype (∑ i, normMap q (v i))=(fixedField q).subtype 1 ↔ _
  exact (fixedField q).subtype.injective.eq_iff

theorem raw_shell_zero (q : CFSG.PrimePower) :
    shellCard (fun a : q.Extension 2 => definingFieldAutomorphism q 2 a*a) 0=0 :=
  shellCard_zero _

theorem raw_shell_succ_recurrence (q : CFSG.PrimePower) (n : ℕ) :
    shellCard (fun a : q.Extension 2 => definingFieldAutomorphism q 2 a*a) (n+1)+
      q.order*shellCard (fun a : q.Extension 2 => definingFieldAutomorphism q 2 a*a) n=
        (q.order+1)*q.order^(2*n) := by
  rw [raw_shell_card_eq,raw_shell_card_eq]
  exact shellCard_succ_recurrence (normMap q) q.order (extension_two_card q)
    (normMap_zero_fibre_card q) (normMap_nonzero_fibre_card q) n

end SymmetricSubgroupAsymptotics.CFSGQuadraticDiagonalNormShell
