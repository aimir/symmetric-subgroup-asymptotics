import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylMonomials
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOrdinaryBorelTwist

/-! Only the ordinary identity and longest Bruhat cells can contain an
actual original Ree-fixed element. This is proved by native permutation
uniqueness and the twelve-label finite calculation. Individual fixed
factor descent is deliberately not inferred from this statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedOrdinaryCells
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoOriginalBorel
open CFSGGTwoOriginalBruhatUniqueness CFSGGTwoOriginalWeylMonomials
open CFSGGTwoOriginalFiniteBruhatCover CFSGGTwoSimpleBruhatComplement
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalAutomorphism
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoOrdinaryBorelTwist
open CFSGReeGTwoOriginalOpposition CFSGGTwoOriginalPositiveRootWords
open CFSGWeylWordBruhatCover CFSGRankTwoSixBraidWords
local notation "A" => CartanMatrix.G₂

theorem fixed_ordinary_two_cells (m : ℕ) (g : originalModelFixed m) :
    g.val∈borel (Field m) ∨
      DoubleCell (borel (Field m)) (longestWord (Field m)) g.val := by
  obtain ⟨k,b,hb,c,hc,he⟩ := original_finite_bruhat (Field m) g.val
  let w := menuWord k
  let n := wordValue (simpleWeyl (Field m)) w
  change g.val=b*n*c at he
  have hf : reeAutomorphism m g.val=g.val := g.property
  have hh := congrArg (reeAutomorphism m) he
  rw [map_mul,map_mul,hf] at hh
  have hp := original_bruhat_cell_permutation_unique (Field m)
    b (reeAutomorphism m b) c (reeAutomorphism m c) n (reeAutomorphism m n)
    hb (ree_borel_mem m b hb) hc (ree_borel_mem m c hc)
    (wordPermutation w) (wordPermutation (w.map CFSG.Models.reverseNode))
    (wordWeight (Field m) w) (twistedWeight (Field m) w)
    (native_word_monomial (Field m) w) (native_ree_word_monomial m w)
    (he.symm.trans hh)
  have hcoord := congrArg (fun s : Equiv.Perm Index=>s (pos 0)) hp
  have hk : k=0 ∨ k=11 := (menu_fixed_permutation k).mp hcoord
  rcases hk with rfl|rfl
  · left
    rw [he]
    change b*1*c∈borel (Field m)
    simpa only [mul_one] using (borel (Field m)).mul_mem hb hc
  · right
    have hn : n=longestWord (Field m) := by
      simp [n,w,menuWord,wordValue,simpleWeyl,longestWord,pow_succ,mul_assoc]
    exact ⟨b,hb,c,hc,he.trans (congrArg (fun z : Model A (Field m)=>b*z*c) hn)⟩

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedOrdinaryCells
