import SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedRelativeGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeyl

/-! Full fixed-field SL-chain words and the paired Weyl word lie in the
literal relative-root subgroup. This is stronger word membership than
membership merely above the original Derived image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeChainLift
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedChainLift CFSGTwistedA2FixedField
open CFSGTwistedDSingularPrefix CFSGTwistedDFixedChainRoots CFSGTwistedDFixedChainParameters
open CFSGTwistedDPairedRootImages CFSGTwistedDRetainedRelativeGroup
open CFSGTwistedDA2MatrixWitness CFSGTwistedDPairedWeyl

def relativePreimage (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)) :=
  (relativeRootGroup (s + 2) q).comap (elementaryRootGroup (q.Extension 2) (s + 4)).subtype

theorem relativePreimage_le_derived (s : ℕ) (q : CFSG.PrimePower) :
    relativePreimage s q ≤ CFSGTwistedDDerivedPairedRoots.naturalDerivedPreimage s q := by
  intro g hg
  have hm := relativeRootGroup_le_derived_unit_image s q
    (show g.val ∈ relativeRootGroup (s + 2) q from hg)
  obtain ⟨h, hh, he⟩ := hm
  have he' : h = g := Subtype.ext he
  simpa only [he'] using hh

theorem parameter_mem (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (i : Fin (s + 2)) (a : fixedField q) :
    naturalRoot s q neg (chainNode (s + 2) i) (a : q.Extension 2) ∈ relativePreimage s q :=
  CFSGTwistedDRelativeElementaryGroup.chain_mem (s + 2) q neg i a

theorem adjacent_chain_mem (s : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (s + 3)) (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) (a : fixedField q) :
    chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) ∈ relativePreimage s q := by
  rcases hadj with hpos | hneg
  · let k : Fin (s + 2) := ⟨i.val, by have := j.isLt; omega⟩
    have hi : chainNode (s + 2) k = i.castSucc := Fin.ext rfl
    have hj : nextCoordinate s k = j.castSucc := Fin.ext hpos
    have hm := parameter_mem s q false k a
    rw [positive_parameter] at hm
    simpa only [hi, hj] using hm
  · let k : Fin (s + 2) := ⟨j.val, by have := i.isLt; omega⟩
    have hj : chainNode (s + 2) k = j.castSucc := Fin.ext rfl
    have hi : nextCoordinate s k = i.castSucc := Fin.ext hneg
    have hm := parameter_mem s q true k a
    rw [negative_parameter] at hm
    simpa only [hi, hj] using hm

theorem fixedChainLift_mem (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q)) :
    CFSGTwistedDFixedChainLift.fixedChainLift s q A ∈ relativePreimage s q := by
  let H := (relativePreimage s q).comap (CFSGTwistedDFixedChainLift.fixedChainLift s q)
  have ht : H = ⊤ := CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent (s + 3) H (by
    intro i j hij hadj a
    change CFSGTwistedDFixedChainLift.fixedChainLift s q
      (CFSGTypeAElementaryMatrices.elementary hij a) ∈ relativePreimage s q
    rw [fixedChainLift_elementary]
    exact adjacent_chain_mem s q i j hij hadj a)
  change A ∈ H
  rw [ht]
  trivial

theorem chain_mem (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 3))
    (hij : i ≠ j) (a : fixedField q) :
    chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) ∈ relativePreimage s q := by
  rw [← fixedChainLift_elementary s q i j hij a]
  exact fixedChainLift_mem s q _

theorem paired_mem (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    pairedNaturalRoot s q neg a ∈ relativePreimage s q := by
  change (pairedNaturalRoot s q neg a).val ∈ relativeRootGroup (s + 2) q
  rw [← pairedRoot_eq_natural]
  exact CFSGTwistedDRelativeElementaryGroup.paired_mem (s + 2) q neg a

theorem pairedWeyl_mem (s : ℕ) (q : CFSG.PrimePower) :
    pairedWeyl s q ∈ relativePreimage s q :=
  (relativePreimage s q).mul_mem
    ((relativePreimage s q).mul_mem (paired_mem s q false (-1)) (paired_mem s q true 1))
    (paired_mem s q false (-1))

theorem conjugate_chain_mem (s : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (s + 3)) (hij : i ≠ j) (a : fixedField q) :
    pairedWeyl s q * chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) *
      (pairedWeyl s q)⁻¹ ∈ relativePreimage s q :=
  (relativePreimage s q).mul_mem
    ((relativePreimage s q).mul_mem (pairedWeyl_mem s q) (chain_mem s q i j hij a))
    ((relativePreimage s q).inv_mem (pairedWeyl_mem s q))

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeChainLift
