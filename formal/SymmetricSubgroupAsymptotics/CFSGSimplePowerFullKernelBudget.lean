import SymmetricSubgroupAsymptotics.ActualSimplePowerFullKernelLiftCount
import SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismPolylogBudget
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts

/-! An actual full-kernel lift budget with all simple automorphism and
order costs discharged internally. The only global theorem input is CFSG;
the displayed kernel chart is retained as genuine original structural data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimplePowerFullKernelBudget
open PrimitiveSocleRawStructure

theorem simple_card_le_least_index_factorial
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    Nat.card D.Simple≤ell.factorial := by
  obtain ⟨H,hH,he⟩ := hell.1
  simpa only [he] using simple_card_le_index_factorial H hH

theorem exists_uniform_full_kernel_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
      {E Q : Type} [Group E] [Group Q] (π : E →* Q) (b : ℕ)
      (e : π.ker ≃* (Fin b → D.Simple)),
      Nat.card (ActualSimplePowerFullKernelLiftCount.Family π b e)≤
        (2*(1+b*ell.factorial^(A*(Nat.log 2 ell+2)^2)))^b := by
  obtain ⟨A,hA⟩ := CFSGSimpleAutomorphismPolylogBudget.exists_uniform_automorphism_budget hCFSG
  refine ⟨A,?_⟩
  intro G X _ _ _ _ D ell hell E Q _ _ π b e
  letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
  have hZ := isCenterless_of_simple_perfect D.Simple
  have ha := (hA D ell hell).trans (Nat.pow_le_pow_left
    (simple_card_le_least_index_factorial D ell hell) (A*(Nat.log 2 ell+2)^2))
  have hb : 2*(1+b*Nat.card (D.Simple ≃* D.Simple))≤
      2*(1+b*ell.factorial^(A*(Nat.log 2 ell+2)^2)) :=
    Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.mul_le_mul_left b ha) 1)
  exact (ActualSimplePowerFullKernelLiftCount.card_family_le π b e hZ).trans
    (Nat.pow_le_pow_left hb b)

end SymmetricSubgroupAsymptotics.CFSGSimplePowerFullKernelBudget
