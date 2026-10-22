import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import SymmetricSubgroupAsymptotics.CFSGIntegerConeAutomorphism

/-! An actual normalizing Weyl word induces an actual permutation of
the coordinate simples preserving the original Cartan matrix. Identity
of that diagram permutation and the torus-kernel question remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagram
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateNormalizerWord
open CFSGIntegerConeAutomorphism
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem normalizer_word_diagram (K : Type) [Field K] (w : List (Fin r))
    (hn : wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) :
    ∃σ : Equiv.Perm (Fin r),
      (∀i,wordRoot A hs hp b₀ s₀ w (s₀ i)=coordinateRoot A hd (σ i)) ∧
      ∀i j,A (σ i) (σ j)=A i j := by
  let e := wordLinear A hs hp b₀ s₀ w
  have he : ∀i : Fin r,0≤e (Pi.single i 1) := by
    intro i l
    change 0≤wordLinear A hs hp b₀ s₀ w (s₀ i:Roots A).val l
    rw [wordLinear_root]
    exact word_simple_nonnegative A hd hs hp ho K w hn i l
  have hi : ∀i : Fin r,0≤e.symm (Pi.single i 1) := by
    intro i l
    change 0≤(wordLinear A hs hp b₀ s₀ w)⁻¹ (Pi.single i 1) l
    rw [←wordLinear_inverseWord]
    change 0≤wordLinear A hs hp b₀ s₀ (inverseWord w) (s₀ i:Roots A).val l
    rw [wordLinear_root]
    exact inverse_word_simple_nonnegative A hd hs hp ho K w hn i l
  obtain ⟨σ,hσ⟩ := permutes_singles_of_simple_images e he hi
  have hroot : ∀i,wordRoot A hs hp b₀ s₀ w (s₀ i)=coordinateRoot A hd (σ i) := by
    intro i
    apply Subtype.ext
    have hh := hσ i
    change wordLinear A hs hp b₀ s₀ w (s₀ i:Roots A).val=(coordinateRoot A hd (σ i)).val at hh
    rw [wordLinear_root] at hh
    exact hh
  refine ⟨σ,hroot,?_⟩
  intro i j
  have hh := wordRoot_integer_pairing A hs hp b₀ s₀ w (s₀ i) (s₀ j)
  rw [hroot i,hroot j] at hh
  change integerPairing A (coordinateRoot A hd (σ i)).val (coordinateRoot A hd (σ j)).val=
    integerPairing A (Pi.single i 1) (Pi.single j 1) at hh
  simpa only [coordinateRoot,integerPairing,Matrix.toBilin'_single] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagram
