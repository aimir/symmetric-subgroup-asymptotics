import SymmetricSubgroupAsymptotics.FourBlockIrreducibleSignedSubgroupLiteralSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily

/-! A complete alternate (2,1) profile for the original parity-coupled
S4 sign action. Both sign flips are words in the actual projected lifts;
the retained sign subgroup is never replaced by the full signed group. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveParityCoupledSignAlternate

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces
open FourBlockSignedSubgroupLiteralSocles
open FourBlockIrreducibleSignedSubgroupLiteralSocles TernaryFourBlockPermutationGenerators
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row282Lifts : Fin 5 → Model (R := Equiv.Perm (Fin 4)) :=
  ![FourBlockSignedSubgroupLiteralSocles.lift (Pi.single 0 1) 0 1,
    FourBlockSignedSubgroupLiteralSocles.lift 0 (pair 0 2) 1,
    FourBlockSignedSubgroupLiteralSocles.lift 0 0 a,
    FourBlockSignedSubgroupLiteralSocles.lift 0 0 b,
    FourBlockSignedSubgroupLiteralSocles.lift 0 (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1) (Equiv.swap 1 3)]

theorem row282_bindings (i : Fin 5) : action 1 (row282Lifts i) = row282Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row282_blocks :
    Subgroup.closure (Set.range (fun i => (row282Lifts i).right.right)) = ⊤ := by
  let B := Subgroup.closure (Set.range (fun i => (row282Lifts i).right.right))
  have hg (i : Fin 5) : (row282Lifts i).right.right ∈ B :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have ha : a ∈ B := by simpa only [row282Lifts,FourBlockSignedSubgroupLiteralSocles.lift,mul_right,right_inl,right_inr,
    one_mul,Matrix.cons_val_succ,Matrix.cons_val_zero] using hg 2
  have hb : b ∈ B := by simpa only [row282Lifts,FourBlockSignedSubgroupLiteralSocles.lift,mul_right,right_inl,right_inr,
    one_mul,Matrix.cons_val_succ,Matrix.cons_val_zero] using hg 3
  have ht : Equiv.swap (1 : Fin 4) 3 ∈ B := by
    simpa only [row282Lifts,FourBlockSignedSubgroupLiteralSocles.lift,mul_right,right_inl,right_inr,
      one_mul,Matrix.cons_val_succ,Matrix.cons_val_zero] using hg 4
  have hs : s ∈ B := by
    have he : b * Equiv.swap 1 3 = s := by decide +kernel
    rw [← he]
    exact B.mul_mem hb ht
  have hc : c ∈ B := by
    have he : a * s = c := by decide +kernel
    rw [← he]
    exact B.mul_mem ha hs
  exact top_unique (fun g _ => symmetric_mem B hc hs g)

theorem row282_sign_pairs :
    evenFlip (R := Equiv.Perm (Fin 4)) 0 1 ∈
      Subgroup.closure (Set.range (fun i => (row282Lifts i).right)) ∧
    evenFlip (R := Equiv.Perm (Fin 4)) 0 2 ∈
      Subgroup.closure (Set.range (fun i => (row282Lifts i).right)) := by
  let S := Subgroup.closure (Set.range (fun i => (row282Lifts i).right))
  have hg (i : Fin 5) : (row282Lifts i).right ∈ S :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have h02 : evenFlip (R := Equiv.Perm (Fin 4)) 0 2 ∈ S := by
    have he : (row282Lifts 1).right = evenFlip (R := Equiv.Perm (Fin 4)) 0 2 := by
      apply SemidirectProduct.ext
      · apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext j
        revert j
        decide +kernel
      · apply Equiv.ext
        intro j
        revert j
        decide +kernel
    rw [← he]
    exact hg 1
  refine ⟨?_,h02⟩
  have he : (row282Lifts 2).right * evenFlip (R := Equiv.Perm (Fin 4)) 0 2 *
      ((row282Lifts 2).right)⁻¹ = evenFlip (R := Equiv.Perm (Fin 4)) 0 1 := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext j
      revert j
      decide +kernel
    · apply Equiv.ext
      intro j
      revert j
      decide +kernel
  rw [← he]
  exact S.mul_mem (S.mul_mem (hg 2) h02) (S.inv_mem (hg 2))

theorem row282AtTwo_quotientSocle (N : Subgroup Row282Top) [N.Normal] :
    SocleNormalGeneratorBound (Row282Top ⧸ N) 2 := by
  apply FourBlockIrreducibleSignedSubgroupLiteralSocles.quotientSocle
    1 row282Lifts row282Generators row282_bindings row282_blocks ?_
    row282_sign_pairs.1 row282_sign_pairs.2 1 1 (by decide)
    symmetric_uniform symmetric_normalGen N
  intro i
  obtain ⟨n,hn⟩ := symmetric_orbit i
  exact ⟨c^n,hn⟩

def row282AtTwo_family : row282Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row282Interface.normalRegistry (fun N => by letI := N.2; exact row282AtTwo_quotientSocle N.1)

def row282AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row282Interface where
  kappa := 2
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row282AtTwo_family
    natural := PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily.row282Natural }

def row282AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (281 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (281 : Fin 301)).finite
      (catalogue.row (281 : Fin 301)).expectedProfiles p :=
  row282AtTwo.resolvedRow hZmud lit _ R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveParityCoupledSignAlternate

end
