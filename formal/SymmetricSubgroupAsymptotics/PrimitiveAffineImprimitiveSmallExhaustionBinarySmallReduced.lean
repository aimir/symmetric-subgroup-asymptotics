import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallExhaustion
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueAcceptedBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace BinarySmallReduced

namespace ComponentSource

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

private abbrev blocks := Nat.card block.Points

private theorem blocks_ne_zero : blocks block ≠ 0 :=
  (Nat.card_pos (α := block.Points)).ne'

private theorem valuation_ge_of_pow_dvd
    {q d : ℕ} (hq : q.Prime) (hpow : q ^ d ∣ blocks block) :
    d ≤ (blocks block).factorization q := by
  exact (hq.pow_dvd_iff_le_factorization (blocks_ne_zero block)).mp hpow

noncomputable def degreeEightExhaustion
    (D : BinaryAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 4 ∨ blocks block = 6) := by
  by_cases h5 : 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) h5
    exact .inl (of_degreeEight_primeFive hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h7 : 7 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 7) h7
    exact .inl (of_degreeEight_primeSeven hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 9 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 9) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3)
          (by norm_num at h9 ⊢; exact h9))
    exact .inl (of_degreeEight_primeThree hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h8 : 2 ^ 3 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 3) h8)
    have he : 3 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h8)
    exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeEight_primeTwo hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 11 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeEight_largePrime hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2 E.one_le E.pow_dvd
        E.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 12 := by
    simpa using dvd_binary_ternary_complement (blocks_ne_zero block)
      (by norm_num) hlarge h5 h7 h9 h8
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs12 : blocks block ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals first
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeEight_threeBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeEight_twelveBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inr ⟨by simp [hs]⟩

noncomputable def degreeSixteenExhaustion
    (D : BinaryAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 4) := by
  by_cases h5 : 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) h5
    exact .inl (of_degreeSixteen_primeFive hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h7 : 7 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 7) h7
    exact .inl (of_degreeSixteen_primeSeven hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 9 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 9) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3)
          (by norm_num at h9 ⊢; exact h9))
    exact .inl (of_degreeSixteen_primeThree hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h32 : 2 ^ 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 5) h32)
    have he : 5 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h32)
    exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_primeTwo hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 11 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeSixteen_largePrime hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2 E.one_le E.pow_dvd
        E.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 48 := by
    simpa using dvd_binary_ternary_complement (blocks_ne_zero block)
      (by norm_num) hlarge h5 h7 h9 h32
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs48 : blocks block ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals first
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_threeBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_sixBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_eightBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_twelveBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_sixteenBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_twentyFourBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.of_degreeSixteen_fortyEightBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inr ⟨by simp [hs]⟩

end ComponentSource

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

