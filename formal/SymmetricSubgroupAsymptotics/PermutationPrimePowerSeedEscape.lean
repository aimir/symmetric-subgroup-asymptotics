import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-! An actual transitive prime-power subgroup above a cardinal threshold
is a conjugacy-invariant upward escape witness. No coverage or classification
assertion is part of this definition or its transport proofs. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
variable {X : Type*}
abbrev Ambient := Equiv.Perm X

def ContainsAbove (p bound : ℕ) (W : Subgroup (Ambient (X := X))) : Prop :=
  ∃ P : Subgroup (Ambient (X := X)), P ≤ W ∧ IsPGroup p P ∧
    PermutationSubgroupTransitive P ∧ bound < Nat.card P

theorem mono (p bound : ℕ) (U V : Subgroup (Ambient (X := X)))
    (hUV : U ≤ V) (hU : ContainsAbove p bound U) : ContainsAbove p bound V := by
  obtain ⟨P, hPU, hp, ht, hcard⟩ := hU
  exact ⟨P, hPU.trans hUV, hp, ht, hcard⟩

theorem conjugate (p bound : ℕ) (c : Ambient (X := X))
    (W : Subgroup (Ambient (X := X))) (hW : ContainsAbove p bound W) :
    ContainsAbove p bound (MulAut.conj c • W) := by
  obtain ⟨P, hPW, hp, ht, hcard⟩ := hW
  refine ⟨MulAut.conj c • P, ?_, ?_,
    permutationSubgroupTransitive_conjugate c P ht, ?_⟩
  · change P.map (MulAut.conj c).toMonoidHom ≤ W.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hPW
  · exact hp.of_equiv (Subgroup.equivSMul (MulAut.conj c) P)
  · have he : Nat.card P = Nat.card ↥(MulAut.conj c • P) :=
      Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) P).toEquiv
    exact hcard.trans_eq he

end SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
end
