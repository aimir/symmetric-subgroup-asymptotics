import SymmetricSubgroupAsymptotics.AdjunctionTargetEscapeCoverage
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape

/-! A normalizer target is stable under every actual seed-normalizing
conjugator. This supports finite adjunction certificates without listing
all subgroups inside that normalizer. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.NormalizerAdjunctionEscapeCoverage

variable {X : Type} [Finite X]
abbrev Ambient := Equiv.Perm X

def Property (p bound : ℕ) (H W : Subgroup (Ambient (X := X))) : Prop :=
  W ≤ Subgroup.normalizer H ∨ PermutationPrimePowerSeedEscape.ContainsAbove p bound W

theorem conjugate (p bound : ℕ) (H : Subgroup (Ambient (X := X)))
    (c : Ambient (X := X)) (hc : MulAut.conj c • H = H)
    (W : Subgroup (Ambient (X := X))) (hW : Property p bound H W) :
    Property p bound H (MulAut.conj c • W) := by
  rcases hW with hsmall | hescape
  · left
    have h := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) hsmall
    rw [Subgroup.map_equiv_normalizer_eq] at h
    have hc' : H.map (MulAut.conj c).toMonoidHom = H := hc
    rw [hc'] at h
    exact h
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate p bound c W hescape)

theorem complete (p bound : ℕ) (H : Subgroup (Ambient (X := X)))
    (hadjoin : ∀ g : Ambient (X := X), Property p bound H (H ⊔ Subgroup.closure {g}))
    (U : Subgroup (Ambient (X := X))) (hHU : H ≤ U) : Property p bound H U :=
  AdjunctionTargetEscapeCoverage.complete H (Subgroup.normalizer H)
    (PermutationPrimePowerSeedEscape.ContainsAbove p bound)
    (fun V W hVW hV => PermutationPrimePowerSeedEscape.mono p bound V W hVW hV)
    hadjoin U hHU

end SymmetricSubgroupAsymptotics.NormalizerAdjunctionEscapeCoverage
end
