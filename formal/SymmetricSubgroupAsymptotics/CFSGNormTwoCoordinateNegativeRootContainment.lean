import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange

/-! Every actual nonpositive lattice-root subgroup lies in literal U-.
The proof uses the original selected Weyl word and the checked word-sign
membership theorem, before any coefficient-field specialization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootContainment
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem selected_negative_root_mem (K : Type) [Field K] (k : Roots A)
    (hk : ∀ i, k.val i ≤ 0) (a : K) :
    selectedRootElement A hd hs hp ho K k a ∈
      CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp b₀ s₀ K true := by
  let p := rootWitness A hd hs hp ho k
  let w := p.val.1 ++ [p.val.2]
  have hroot : wordRoot A hs hp b₀ s₀ w (s₀ p.val.2) = k := by
    apply Subtype.ext
    calc
      _ = wordLinear A hs hp b₀ s₀ w (s₀ p.val.2 : Roots A).val :=
        (wordLinear_root A hs hp b₀ s₀ w (s₀ p.val.2)).symm
      _ = wordLinear A hs hp b₀ s₀ p.val.1 (-(s₀ p.val.2 : Roots A).val) := by
        dsimp only [w]
        rw [wordLinear_append]
        change wordLinear A hs hp b₀ s₀ p.val.1
          (reflectionEquiv A (s₀ p.val.2) (s₀ p.val.2 : Roots A).val) = _
        congr 1
        change (s₀ p.val.2 : Roots A).val -
          integerPairing A (s₀ p.val.2 : Roots A).val (s₀ p.val.2 : Roots A).val •
            (s₀ p.val.2 : Roots A).val = -(s₀ p.val.2 : Roots A).val
        rw [(s₀ p.val.2 : Roots A).property]
        module
      _ = k.val := p.property.symm
  have hneg : ∀ j, (wordRoot A hs hp b₀ s₀ w (s₀ p.val.2)).val j ≤ 0 := by
    rw [hroot]
    exact hk
  have hmem := CFSGNormTwoCoordinateWeylRootMembership.negative_word_mem
    A hd hs hp ho K w p.val.2 (-a) hneg
  have hword : wordUnit A hs hp b₀ s₀ K w =
      canonicalWord D K p.val.1 * canonicalWeyl D K p.val.2 := by
    dsimp only [w]
    rw [wordUnit_append]
    simp only [wordUnit, mul_one, word_eq_canonicalWord]
  have he : selectedRootElement A hd hs hp ho K k a =
      CFSGNormTwoCoordinateWeylRootMembership.rootWord A hd hs hp ho K w p.val.2 (-a) := by
    rw [CFSGNormTwoCoordinateWeylRootMembership.rootWord, hword]
    let u := canonicalWord D K p.val.1
    change u * canonicalRoot D K true p.val.2 a * u⁻¹ =
      (u * canonicalWeyl D K p.val.2) * canonicalRoot D K false p.val.2 (-a) *
        (u * canonicalWeyl D K p.val.2)⁻¹
    have hself := CFSGNormTwoGeckSelfRootConjugation.self_root_word A hs hp b₀ s₀ K p.val.2 (-a)
    simp only [neg_neg] at hself
    rw [← hself]
    group
  rw [he]
  exact hmem

theorem negative_root_subgroup_le (K : Type) [Field K] (k : Roots A)
    (hk : ∀ i, k.val i ≤ 0) :
    rootSubgroup A hd hs hp ho K k ≤
      CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp b₀ s₀ K true := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
  exact selected_negative_root_mem A hd hs hp ho K k hk a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootContainment
