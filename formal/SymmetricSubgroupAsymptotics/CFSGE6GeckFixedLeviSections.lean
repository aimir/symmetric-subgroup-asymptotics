import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedHeightGeneration
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveOrbitFactors
import SymmetricSubgroupAsymptotics.CFSGComplementGradingFactor
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Diagram-fixed positive sections detect an actual preserving factor.
The hypotheses give section membership, normalization, and two disjoint
matrix grading subgroups. Coverage is a conclusion of fixed-height
generation and the literal subgroup product, not a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedLeviSections
open CFSGE6GeckFixedHeightGeneration CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGFFourE6PositiveOrbitFactors
open CFSGGradedMatrixSubgroups CFSGComplementGradingFactor

theorem fixed_mem_sup_of_root_sections (K : Type) [Field K] [Finite K]
    (N M : Subgroup (Positive K))
    (hsingle : ∀ (k : PositiveRoot), diagramRoot k.val = k.val → ∀ x : RootLine K k.val,
      unitTwist K (RingEquiv.refl K) x.val = x.val → rootLinePositive K k x ∈ N ⊔ M)
    (hpair : ∀ (k : PositiveRoot), diagramRoot k.val ≠ k.val → ∀ x : RootLine K k.val,
      rootLinePositive K k x *
        positiveTwist K (RingEquiv.refl K) (rootLinePositive K k x) ∈ N ⊔ M)
    (u : Positive K) (hu : positiveTwist K (RingEquiv.refl K) u = u) : u ∈ N ⊔ M := by
  let F : Subgroup (Positive K) :=
    (positiveTwist K (RingEquiv.refl K)).toMonoidHom.eqLocus (MonoidHom.id (Positive K))
  let S : Subgroup (Positive K) := (N ⊔ M) ⊓ F
  have hSfixed : ∀ a ∈ S, positiveTwist K (RingEquiv.refl K) a = a :=
    fun _ ha => ha.2
  have hs : ∀ (k : PositiveRoot), diagramRoot k.val = k.val → ∀ x : RootLine K k.val,
      unitTwist K (RingEquiv.refl K) x.val = x.val → rootLinePositive K k x ∈ S := by
    intro k hk x hx
    refine ⟨hsingle k hk x hx, ?_⟩
    change positiveTwist K (RingEquiv.refl K) (rootLinePositive K k x) =
      rootLinePositive K k x
    exact Subtype.ext hx
  have hp : ∀ (k : PositiveRoot), diagramRoot k.val ≠ k.val → ∀ x : RootLine K k.val,
      rootLinePositive K k x * positiveTwist K (RingEquiv.refl K)
        (rootLinePositive K k x) ∈ S := by
    intro k hk x
    refine ⟨hpair k hk x, ?_⟩
    have h := rootOrbitFactor_fixed K k x
    rw [rootOrbitFactor, if_neg hk] at h
    exact h
  exact (fixed_mem_of_root_sections K (RingEquiv.refl K) S hSfixed hs hp u hu).1

theorem fixed_mem_right_of_sections (K : Type) [Field K] [Finite K]
    (N M : Subgroup (Positive K)) (weight : GeckIndex → ℤ)
    (hMN : M ≤ Subgroup.normalizer (N : Set (Positive K)))
    (hN : N.map (Positive K).subtype ≤ strictUnits weight)
    (hM : M.map (Positive K).subtype ≤ preservingUnits weight)
    (hsingle : ∀ (k : PositiveRoot), diagramRoot k.val = k.val → ∀ x : RootLine K k.val,
      unitTwist K (RingEquiv.refl K) x.val = x.val → rootLinePositive K k x ∈ N ⊔ M)
    (hpair : ∀ (k : PositiveRoot), diagramRoot k.val ≠ k.val → ∀ x : RootLine K k.val,
      rootLinePositive K k x *
        positiveTwist K (RingEquiv.refl K) (rootLinePositive K k x) ∈ N ⊔ M)
    (u : Positive K) (hu : positiveTwist K (RingEquiv.refl K) u = u)
    (hpres : u.val ∈ preservingUnits weight) : u ∈ M := by
  have hm := fixed_mem_sup_of_root_sections K N M hsingle hpair u hu
  change u ∈ (↑(N ⊔ M) : Set (Positive K)) at hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N M hMN] at hm
  obtain ⟨n, hn, l, hl, he⟩ := hm
  have heRaw : u.val = n.val * l.val :=
    congrArg (fun g : Positive K => g.val) he.symm
  have hr : u.val ∈ M.map (Positive K).subtype :=
    mem_right_of_factor hN hM (strict_inf_preserving weight)
      (show n.val ∈ N.map (Positive K).subtype from ⟨n, hn, rfl⟩)
      (show l.val ∈ M.map (Positive K).subtype from ⟨l, hl, rfl⟩) heRaw hpres
  obtain ⟨v, hv, hvu⟩ := hr
  have heq : v = u := Subtype.ext hvu
  exact heq ▸ hv

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedLeviSections
