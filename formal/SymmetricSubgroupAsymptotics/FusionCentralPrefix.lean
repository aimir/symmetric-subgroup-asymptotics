import SymmetricSubgroupAsymptotics.FusionCentralLifts

/-!
# The actual central-cut Schur envelope and joint graph moment

The original tower Q → R → B is retained. Its first kernel is central and
binary, while its second has the supplied actual binary module chart.
No extension is assumed split, and every character/quotient column uses
one complete source. The central marker is inside Φ; the Schur tail is not.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The retained same-source base maps and binary characters. -/
def fusionCentralPrefixWeight (c : ℕ) (J B : Type*) [Group J] [Group B] : ℝ :=
  (Nat.card (GroupEpimorphism J B) : ℝ)*(2:ℝ)^(c*binaryCharacterRank J)

section Envelope

variable {J Q R B V : Type} [Group J] [Group Q] [Group R] [Group B]
variable [Finite J] [Finite Q] [Finite R] [Finite B]
variable [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The central-cut envelope on the original surviving epi family.
The only numerical input is the rank bound on actual Sylow/Frattini
quotients. All remaining factors follow from actual extension fibres. -/
theorem fusionCentralPrefix_survival_card_le
    (π : Q →* R) (hπ : Function.Surjective π) (hC : FusionCentralKernel π)
    (EC : π.ker ≃* Multiplicative V)
    (α : R →* B) (hα : Function.Surjective α)
    (M : Rep (ZMod 2) B) [Finite M] (E : OriginalKernelModuleChart α M)
    (P : ∀ β : GroupEpimorphism J B, Sylow 2 β.1.ker)
    (S : GroupEpimorphism J Q → Prop) (b : ℝ)
    (hrank : ∀ β : GroupEpimorphism J B,
      (Module.finrank (ZMod 2) (PrimeAbelianization 2 (P β : Subgroup β.1.ker)) : ℝ)≤b/2) :
    (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      (Nat.card M * Nat.card (groupCohomology.H1 M) : ℝ) *
        (2:ℝ)^((representationSchurCapacity M.ρ/2)*b) *
          fusionCentralPrefixWeight (Module.finrank (ZMod 2) V) J B := by
  have hc := fusionCentralBinaryEpimorphism_survival_card_le π hπ hC EC S
  have hcR : (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      (Nat.card (GroupEpimorphism J R) : ℝ)*
        (2:ℝ)^(Module.finrank (ZMod 2) V*binaryCharacterRank J) := by exact_mod_cast hc
  have hs := fusionEpimorphism_survival_card_le_schur_of_rank_bound 2 α hα M E P
    (fun _ => True) b hrank
  rw [Nat.card_subtype_true] at hs
  calc
    _ ≤ (Nat.card (GroupEpimorphism J R) : ℝ)*
        (2:ℝ)^(Module.finrank (ZMod 2) V*binaryCharacterRank J) := hcR
    _ ≤ (Nat.card (GroupEpimorphism J B) *
        (Nat.card M * Nat.card (groupCohomology.H1 M) *
          (2:ℝ)^(representationSchurCapacity M.ρ*(b/2)))) *
            (2:ℝ)^(Module.finrank (ZMod 2) V*binaryCharacterRank J) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by
      unfold fusionCentralPrefixWeight
      rw [show representationSchurCapacity M.ρ*(b/2)=
        (representationSchurCapacity M.ρ/2)*b by ring]
      ring

end Envelope

/-- The envelope's entire Φ is encoded by actual common-source columns.
Repeated maps and dependent binary characters are allowed; the original
complete source and every physical cover/marker block are recovered. -/
theorem fusionCentralPrefixWeight_moment_le {A B : Type*} [Group A] [Group B] {s : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (π : A →* B) (hπ : Function.Surjective π) (b c q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCentralPrefixWeight c J B^q) ≤
      (subgroupCount (b+q*(s+2*c)) : ℝ) := by
  have hm := jointSourceEpimorphism_binaryRank_moment_le ρ hρ π hπ b c q
  unfold fusionCentralPrefixWeight
  exact_mod_cast hm

end SymmetricSubgroupAsymptotics
