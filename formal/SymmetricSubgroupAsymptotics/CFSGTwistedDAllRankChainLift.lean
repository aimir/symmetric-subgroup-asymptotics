import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllRankQuadraticPreservation
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedForkRoots

/-! The actual fixed-field SL block belongs to the literal relative-root
group already in rank three. The proof retains exact adjacent roots;
no original Derived or low-rank classical recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGOrthogonalDGenerationRootArrays CFSGTwistedDA2MatrixWitness
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDSingularPrefix
open CFSGTwistedA2FixedField CFSGTypeAElementaryMatrices CFSGSpecialLinearLastBlock
open CFSGOrthogonalDAllRankQuadraticPreservation

def chainLift (n : ℕ) (q : CFSG.PrimePower) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q) →*
      (Mat (q.Extension 2) (n + 2))ˣ :=
  (doubleHom (q.Extension 2) (n + 2)).comp
    ((lastBlockHom (q.Extension 2) (n + 1)).comp
      (Matrix.SpecialLinearGroup.map (fixedField q).subtype))

theorem chainLift_elementary (n : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (n + 1)) (hij : i ≠ j) (a : fixedField q) :
    chainLift n q (elementary hij a) =
      (chain (q.Extension 2) (n + 2) i.castSucc j.castSucc
        ((Fin.castSucc_injective (n + 1)).ne hij) (a : q.Extension 2)).val := by
  change doubleHom (q.Extension 2) (n + 2)
    (lastBlockHom (q.Extension 2) (n + 1)
      (Matrix.SpecialLinearGroup.map (fixedField q).subtype (elementary hij a))) = _
  rw [CFSGTwistedDFixedChainLift.map_elementary, lastBlockHom_elementary]
  rfl

theorem adjacent_chain_mem (n : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (n + 1)) (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) (a : fixedField q) :
    (chain (q.Extension 2) (n + 2) i.castSucc j.castSucc
      ((Fin.castSucc_injective (n + 1)).ne hij) (a : q.Extension 2)).val ∈ relativeRootGroup n q := by
  rcases hadj with hpos | hneg
  · let k : Fin n := ⟨i.val, by have := j.isLt; omega⟩
    have hk : chainNode n k = i.castSucc := Fin.ext rfl
    have hi : i.castSucc.val + 1 < n + 2 := by have := i.isLt; simp only [Fin.val_castSucc]; omega
    have hnext : (⟨i.castSucc.val + 1, hi⟩ : Fin (n + 2)) = j.castSucc := Fin.ext hpos
    have hm := CFSGTwistedDRelativeElementaryGroup.chain_mem n q false k a
    rw [hk] at hm
    have he : rootTransvection (q.Extension 2) (n + 2) false i.castSucc (a : q.Extension 2) =
        (chain (q.Extension 2) (n + 2) i.castSucc j.castSucc
          ((Fin.castSucc_injective (n + 1)).ne hij) (a : q.Extension 2)).val := by
      apply Units.ext
      rw [nonterminal_root_array _ n false _ hi]
      simp only [Bool.false_eq_true, if_false, hnext]
      rw [CFSGTwistedDRetainedForkRoots.chain_val]
      rfl
    rw [he] at hm
    exact hm
  · let k : Fin n := ⟨j.val, by have := i.isLt; omega⟩
    have hk : chainNode n k = j.castSucc := Fin.ext rfl
    have hi : j.castSucc.val + 1 < n + 2 := by have := j.isLt; simp only [Fin.val_castSucc]; omega
    have hnext : (⟨j.castSucc.val + 1, hi⟩ : Fin (n + 2)) = i.castSucc := Fin.ext hneg
    have hm := CFSGTwistedDRelativeElementaryGroup.chain_mem n q true k a
    rw [hk] at hm
    have he : rootTransvection (q.Extension 2) (n + 2) true j.castSucc (a : q.Extension 2) =
        (chain (q.Extension 2) (n + 2) i.castSucc j.castSucc
          ((Fin.castSucc_injective (n + 1)).ne hij) (a : q.Extension 2)).val := by
      apply Units.ext
      rw [nonterminal_root_array _ n true _ hi]
      simp only [if_true, hnext]
      rw [CFSGTwistedDRetainedForkRoots.chain_val]
      rfl
    rw [he] at hm
    exact hm

theorem chainLift_mem (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q)) :
    chainLift n q A ∈ relativeRootGroup n q := by
  let H := (relativeRootGroup n q).comap (chainLift n q)
  have ht : H = ⊤ := CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent (n + 1) H (by
    intro i j hij hadj a
    change chainLift n q (elementary hij a) ∈ relativeRootGroup n q
    rw [chainLift_elementary]
    exact adjacent_chain_mem n q i j hij hadj a)
  change A ∈ H
  rw [ht]
  trivial

theorem chain_mem (n : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (n + 1)) (hij : i ≠ j) (a : fixedField q) :
    (chain (q.Extension 2) (n + 2) i.castSucc j.castSucc
      ((Fin.castSucc_injective (n + 1)).ne hij) (a : q.Extension 2)).val ∈ relativeRootGroup n q := by
  rw [← chainLift_elementary n q i j hij a]
  exact chainLift_mem n q _

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
