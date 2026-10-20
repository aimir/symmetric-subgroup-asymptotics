import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.PrimeLayerVanishing
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-! Removing a kernel of coprime prime-power exponent preserves a sectional
prime-rank bound. Every test subgroup uses its own image and literal kernel;
no fullness of a projection or normality of the test subgroup is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- A homomorphism with coprime power-group kernel pulls a sectional bound
back from its target, without needing surjectivity onto the target. -/
theorem PrimeSectionalRankBound.of_power_kernel
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (q : ℕ) (hq : (q : ZMod p) ≠ 0) (f : G →* Q)
    (hker : IsPGroup q f.ker) {r : ℕ}
    (hQ : PrimeSectionalRankBound p Q r) : PrimeSectionalRankBound p G r := by
  intro K
  let ψ : K →* Q := f.comp K.subtype
  let π : K →* ψ.range := ψ.rangeRestrict
  let j : π.ker →* f.ker := {
    toFun := fun x => ⟨(x.1 : G), by
      have hx := congrArg (fun y : ψ.range => (y : Q)) x.2
      exact hx⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : G)) hxy
  have hz : Module.finrank (ZMod p) (primeRelativeCharacters p π.ker) = 0 :=
    primeRelativeHead_power_group p π.ker q hq (hker.of_injective j hj)
  have hext := primeCharacterRank_extension_le p π ψ.rangeRestrict_surjective
  rw [hz, Nat.add_zero] at hext
  exact hext.trans (hQ ψ.range)

/-- A faithful permutation target bounds every subgroup after discarding
only the displayed coprime power-group kernel. -/
theorem primeSectionalRankBound_of_power_kernel_permutation
    {G Q X : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Finite X] [MulAction Q X] [FaithfulSMul Q X]
    (q : ℕ) (hq : (q : ZMod p) ≠ 0) (f : G →* Q)
    (hker : IsPGroup q f.ker) : PrimeSectionalRankBound p G (Nat.card X / p) :=
  PrimeSectionalRankBound.of_power_kernel p q hq f hker
    (fun K => permutation_primeCharacterRank_le p K X)

end SymmetricSubgroupAsymptotics

end
