import SymmetricSubgroupAsymptotics.BinarySubdirectJointTransition
import SymmetricSubgroupAsymptotics.JointCapacitySupport

/-! The marked one-peel transition on the original full subdirect group.
The same source supplies character rank, the maximum over derived normals,
and the actual terminal H² defect. No positive-sign assumption is made on
the first mark. This is the local input to the carrier word recurrence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (K : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype))

include hB

/-- An arbitrary first mark and nonnegative other marks follow the same
coupled polygon, including the retained radical in the H² term. -/
theorem binarySubdirect_marked_transition (x y z : ℝ) (hy : 0≤y) (hz : 0≤z) :
    letI := Subgroup.normal_goursatFst hA
    let k := Module.finrank (ZMod 2) (primeRelativeCharacters 2 K.goursatFst)
    let m := primeSubdirectAxisNormalRank 2 K
    let a₂ := Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 K.goursatFst))
    x*(Module.finrank (ZMod 2) (PrimeCharacters 2 K) : ℝ) +
      y*(primeDerivedNormalRank 2 K : ℝ) +
      z*(Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K) : ℝ) ≤
    x*(Module.finrank (ZMod 2) (PrimeCharacters 2 B) : ℝ) +
      y*(primeDerivedNormalRank 2 B : ℝ) +
      z*(Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B) : ℝ) +
      z*((k : ℝ)+(max m a₂ : ℕ)) +
      jointCapacitySupport k (Nat.log 2 (Nat.card K.goursatFst)) m (x-z) y := by
  letI := Subgroup.normal_goursatFst hA
  obtain ⟨hmono,hδ,hε,hjoint,hτ⟩ := binarySubdirect_joint_transition K hA hB
  exact jointCapacity_marked_transition
    (d₀ := Module.finrank (ZMod 2) (PrimeCharacters 2 B))
    (d₁ := Module.finrank (ZMod 2) (PrimeCharacters 2 K))
    (ρ₀ := primeDerivedNormalRank 2 B) (ρ₁ := primeDerivedNormalRank 2 K)
    (τ₀ := Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B))
    (τ₁ := Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K))
    (by omega) (by omega) (by omega) hδ hε hjoint x y z hy hz

/-- The initial terminal mark has its sharp one-peel cost even when j−2ℓ
is negative. Later nonnegative epimorphism tilts are handled by support
subadditivity, without replacing the actual source by independent factors. -/
theorem binarySubdirect_terminal_mark_le (j ell : ℝ) (hell : 0≤ell) :
    letI := Subgroup.normal_goursatFst hA
    let k := Module.finrank (ZMod 2) (primeRelativeCharacters 2 K.goursatFst)
    let m := primeSubdirectAxisNormalRank 2 K
    let a₂ := Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 K.goursatFst))
    (j-ell)*(Module.finrank (ZMod 2) (PrimeCharacters 2 K) : ℝ) +
      ell*(Module.finrank (ZMod 2) (terminalRestrictedInflationKernel K) : ℝ) ≤
    (j-ell)*(Module.finrank (ZMod 2) (PrimeCharacters 2 B) : ℝ) +
      ell*(Module.finrank (ZMod 2) (terminalRestrictedInflationKernel B) : ℝ) +
      ell*((k : ℝ)+(max m a₂ : ℕ))+(k : ℝ)*max (j-2*ell) 0 := by
  letI := Subgroup.normal_goursatFst hA
  have h := binarySubdirect_marked_transition K hA hB (j-ell) 0 ell le_rfl hell
  have hs := jointCapacitySupport_zero_second_le
    (Module.finrank (ZMod 2) (primeRelativeCharacters 2 K.goursatFst))
    (Nat.log 2 (Nat.card K.goursatFst)) (primeSubdirectAxisNormalRank 2 K) (j-2*ell)
  have he : j-ell-ell=j-2*ell := by ring
  simp only [zero_mul,add_zero,he] at h
  dsimp only
  linarith

end SymmetricSubgroupAsymptotics
