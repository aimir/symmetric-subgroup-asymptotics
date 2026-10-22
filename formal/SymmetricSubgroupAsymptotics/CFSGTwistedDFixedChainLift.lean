import SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlock
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedChainParameters

/-! The actual fixed-field SL block on all coordinates except the last
has image in the SAME original Derived preimage. This is proved from
the full-parameter adjacent chain lines, rather than a fixed-group
identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainLift
open CFSGTypeAElementaryMatrices CFSGSpecialLinearLastBlock
open CFSGTwistedA2FixedField CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDGenerationSLDouble CFSGTwistedDA2MatrixWitness
open CFSGTwistedDSingularPrefix CFSGTwistedDFixedChainRoots
open CFSGTwistedDFixedChainParameters CFSGTwistedDDerivedPairedRoots

theorem map_elementary {F K I : Type} [Field F] [Field K]
    [Fintype I] [DecidableEq I] (f : F →+* K)
    (i j : I) (hij : i ≠ j) (a : F) :
    Matrix.SpecialLinearGroup.map f (elementary hij a) = elementary hij (f a) := by
  apply Subtype.ext
  ext x y
  simp [Matrix.SpecialLinearGroup.map, Matrix.transvection, Matrix.single_apply,
    Matrix.one_apply] <;> split_ifs <;> simp_all

def fixedChainLift (s : ℕ) (q : CFSG.PrimePower) :
    Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q) →*
      elementaryRootGroup (q.Extension 2) (s + 4) :=
  (doubleIntoElementary (q.Extension 2) (s + 4)).comp
    ((lastBlockHom (q.Extension 2) (s + 3)).comp
      (Matrix.SpecialLinearGroup.map (fixedField q).subtype))

theorem fixedChainLift_elementary (s : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (s + 3)) (hij : i ≠ j) (a : fixedField q) :
    fixedChainLift s q (elementary hij a) =
      chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
        ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) := by
  change doubleIntoElementary (q.Extension 2) (s + 4)
    (lastBlockHom (q.Extension 2) (s + 3)
      (Matrix.SpecialLinearGroup.map (fixedField q).subtype (elementary hij a))) = _
  rw [map_elementary, lastBlockHom_elementary]
  rfl

theorem chain_adjacent_mem (s : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (s + 3)) (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) (a : fixedField q) :
    chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) ∈ naturalDerivedPreimage s q := by
  have ha : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 (a : q.Extension 2) = a :=
    a.property
  rcases hadj with hpos | hneg
  · let k : Fin (s + 2) := ⟨i.val, by have := j.isLt; omega⟩
    have hi : chainNode (s + 2) k = i.castSucc := Fin.ext rfl
    have hj : nextCoordinate s k = j.castSucc := Fin.ext hpos
    have hm := CFSGTwistedDDerivedChainParameters.parameter_mem_derived_preimage s q false k a ha
    rw [positive_parameter] at hm
    simpa only [hi, hj] using hm
  · let k : Fin (s + 2) := ⟨j.val, by have := i.isLt; omega⟩
    have hj : chainNode (s + 2) k = j.castSucc := Fin.ext rfl
    have hi : nextCoordinate s k = i.castSucc := Fin.ext hneg
    have hm := CFSGTwistedDDerivedChainParameters.parameter_mem_derived_preimage s q true k a ha
    rw [negative_parameter] at hm
    simpa only [hi, hj] using hm

theorem fixedChainLift_mem (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q)) :
    fixedChainLift s q A ∈ naturalDerivedPreimage s q := by
  let H := (naturalDerivedPreimage s q).comap (fixedChainLift s q)
  have ht : H = ⊤ := CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent (s + 3) H (by
    intro i j hij hadj a
    change fixedChainLift s q (elementary hij a) ∈ naturalDerivedPreimage s q
    rw [fixedChainLift_elementary]
    exact chain_adjacent_mem s q i j hij hadj a)
  change A ∈ H
  rw [ht]
  trivial

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainLift
