import SymmetricSubgroupAsymptotics.CFSGFFourE6PrimitiveWeights
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality

/-! The four actual folded Cartan weights of every positive E6 root
have an integral linear combination equal to one. Consequently at least
one weight survives in EVERY nontrivial coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedWeights
open CFSGFFourE6PrimitiveWeights CFSGTwistedE6GeckOriginalRootSections
open CFSGCartanDiagramLinearAction CFSGSerreDiagram CFSGIntegerMatrixPairing

def orbitCartan (i : Fin 4) : Fin 6 → ℤ :=
  ![Pi.single 0 1 + Pi.single 5 1, Pi.single 2 1 + Pi.single 4 1,
    Pi.single 3 1, Pi.single 1 1] i

theorem fixed_vector_decomposition (h : Fin 6 → ℤ)
    (hh : permutationLinear e6Permutation h=h) :
    h = h 0 • orbitCartan 0 + h 2 • orbitCartan 1 +
      h 3 • orbitCartan 2 + h 1 • orbitCartan 3 := by
  have h5 := congrFun hh (5 : Fin 6)
  have h4 := congrFun hh (4 : Fin 6)
  change h (e6Permutation.symm 5)=h 5 at h5
  change h (e6Permutation.symm 4)=h 4 at h4
  rw [CFSGTwistedE6DiagramRootOrthogonality.diagramPermutation_symm] at h5 h4
  change h 0=h 5 at h5
  change h 2=h 4 at h4
  funext i
  fin_cases i <;> simp [orbitCartan,Pi.single_apply,smul_eq_mul,h5,h4]

def foldedWeight (k : PositiveRoot) (i : Fin 4) : ℤ :=
  integerPairing CartanMatrix.E₆ k.val.val (orbitCartan i)

theorem foldedWeights_generate_one (k : PositiveRoot) :
    ∃a : Fin 4 → ℤ,
      a 0 * foldedWeight k 0 + a 1 * foldedWeight k 1 +
        a 2 * foldedWeight k 2 + a 3 * foldedWeight k 3 = 1 := by
  let h := primitiveTest k
  refine ⟨![h 0,h 2,h 3,h 1],?_⟩
  change h 0 * foldedWeight k 0 + h 2 * foldedWeight k 1 +
    h 3 * foldedWeight k 2 + h 1 * foldedWeight k 3 = 1
  have hp := primitiveTest_pairing k
  rw [fixed_vector_decomposition (primitiveTest k) (primitiveTest_fixed k)] at hp
  simpa only [map_add,map_smul,smul_eq_mul,foldedWeight,h] using hp

theorem exists_foldedWeight_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (k : PositiveRoot) :
    ∃i : Fin 4,(foldedWeight k i : R)≠0 := by
  by_contra hn
  have hz : ∀i : Fin 4,(foldedWeight k i : R)=0 := by simpa only [not_exists,not_not] using hn
  obtain ⟨a,ha⟩ := foldedWeights_generate_one k
  have he := congrArg (Int.cast : ℤ → R) ha
  simp only [Int.cast_add,Int.cast_mul,Int.cast_one,hz,mul_zero,add_zero] at he
  exact zero_ne_one he

end SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedWeights
