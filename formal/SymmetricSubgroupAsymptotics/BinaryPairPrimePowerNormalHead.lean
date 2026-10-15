import SymmetricSubgroupAsymptotics.BinaryPairNormalHead
import SymmetricSubgroupAsymptotics.PrimePowerPermutationHead
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-!
Relative binary heads of every original normal subgroup of a pair action.
The intersection with the actual pair kernel has its own correlated flip
subspace. A Sylow semiregular element bounds that subspace's head, and the
relative exact sequence adds the head of the actual normal top image.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Finite X] [Finite I] [Nontrivial I]
  {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
  [MulAction U I] [MulAction.IsPretransitive U I]
  (hact : ∀ (u : U) (i : I), u • i = F.top u i)

include hact in
/-- This bound does not require the original group to be binary. -/
theorem normal_kernel_relativeHead_le_half
    {a : ℕ} (hcard : Nat.card I = 2 ^ a)
    (N : Subgroup U) [N.Normal] (hN : N ≤ F.top.ker) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ Nat.card I / 2 := by
  rw [← (F.normalKernelOriginalCharactersEquiv hact N hN).finrank_eq,
    (representationCharacterHeadEquiv
      (F.normalKernelOriginalSubrepresentation hact N hN).toRepresentation).finrank_eq]
  exact primePower_permutationSubrepresentationHead_le_div (p := 2) hcard
    (F.normalKernelOriginalSubrepresentation hact N hN)

include hact in
/-- Both terms refer to the original normal subgroup and its literal image
under F.top. No normal-head monotonicity is used. -/
theorem relativeHead_le_half_add_top
    {a : ℕ} (hcard : Nat.card I = 2 ^ a) (rank : ℕ)
    (htop : ∀ (M : Subgroup F.top.range) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ rank)
    (N : Subgroup U) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ Nat.card I / 2 + rank := by
  have hchain := primeRelativeHead_chain_le (N ⊓ F.top.ker) N 2 inf_le_left
  rw [primeRelativeHead_second_isomorphism,
    primeRelativeHead_original_range] at hchain
  exact hchain.trans (Nat.add_le_add
    (F.normal_kernel_relativeHead_le_half hact hcard (N ⊓ F.top.ker) inf_le_right)
    (htop (originalNormalRange F.top N)))

include hact in
/-- Four scalar coordinates plus the checked top rank two suffice for the
sixteen-point branch; a sharper scalar bound is unnecessary here. -/
theorem eightPair_relativeHead_le_six
    (hcard : Nat.card I = 8)
    (htop : ∀ (M : Subgroup F.top.range) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2)
    (N : Subgroup U) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 6 := by
  have hpow : Nat.card I = 2 ^ 3 := by simpa only [hcard] using (by decide : 8 = 2 ^ 3)
  simpa only [hcard] using F.relativeHead_le_half_add_top hact hpow 2 htop N

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
