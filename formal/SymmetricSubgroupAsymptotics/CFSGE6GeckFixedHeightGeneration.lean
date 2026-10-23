import SymmetricSubgroupAsymptotics.CFSGE6GeckHeightSubgroupLifting
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveSourceImage

/-! Genuine fixed root sections generate the whole twist-fixed upper group.
The subgroup supplies fixed singleton sections and the literal paired
products; the finite height filtration supplies the conclusion. In
particular, surjectivity on fixed height quotients is proved by the
root-section construction, rather than assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedHeightGeneration
open CFSGE6GeckHeightSubgroupLifting CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckIntrinsicHeightAction
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckHeightQuotientTwist CFSGTwistedE6GeckFixedHeightOrbitLifting
open CFSGTwistedE6GeckFixedPositiveSourceImage CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightBound

local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

theorem exists_subgroup_height_factor (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (S : Subgroup (Positive K))
    (hSfixed : ∀ a ∈ S, positiveTwist K sigma a = a)
    (hsingle : ∀ (k : PositiveRoot), diagramRoot k.val = k.val → ∀ x : RootLine K k.val,
      unitTwist K sigma x.val = x.val → rootLinePositive K k x ∈ S)
    (hpair : ∀ (k : PositiveRoot), diagramRoot k.val ≠ k.val → ∀ x : RootLine K k.val,
      rootLinePositive K k x * positiveTwist K sigma (rootLinePositive K k x) ∈ S)
    (h : ℤ) (hh : 0 < h) (u : Positive K) (hu : u ∈ TailInPositive K h)
    (hfixed : positiveTwist K sigma u = u) :
    ∃ a : Positive K, a ∈ S ∧ ∃ v : Positive K,
      v ∈ TailInPositive K (h + 1) ∧ positiveTwist K sigma v = v ∧ u = a * v := by
  let x : HeightImage K h := ⟨heightClass K h u, ⟨u, hu, rfl⟩⟩
  have hx : heightImageTwist K sigma h x = x := by
    apply Subtype.ext
    change quotientTwist K sigma h (QuotientGroup.mk' (TailInPositive K (h + 1)) u) =
      QuotientGroup.mk' (TailInPositive K (h + 1)) u
    rw [quotientTwist_mk, hfixed]
  obtain ⟨a, ha, _, he⟩ := fixed_height_class_lift K sigma S hsingle hpair h hh x hx
  have hv : a⁻¹ * u ∈ TailInPositive K (h + 1) := by
    have hk : a⁻¹ * u ∈ (heightClass K h).ker := by
      change heightClass K h (a⁻¹ * u) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    change a⁻¹ * u ∈ (QuotientGroup.mk' (TailInPositive K (h + 1))).ker at hk
    rwa [QuotientGroup.ker_mk'] at hk
  refine ⟨a, ha, a⁻¹ * u, hv, ?_, (mul_inv_cancel_left a u).symm⟩
  rw [map_mul, map_inv, hSfixed a ha, hfixed]

theorem fixed_mem_of_root_sections (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (S : Subgroup (Positive K))
    (hSfixed : ∀ a ∈ S, positiveTwist K sigma a = a)
    (hsingle : ∀ (k : PositiveRoot), diagramRoot k.val = k.val → ∀ x : RootLine K k.val,
      unitTwist K sigma x.val = x.val → rootLinePositive K k x ∈ S)
    (hpair : ∀ (k : PositiveRoot), diagramRoot k.val ≠ k.val → ∀ x : RootLine K k.val,
      rootLinePositive K k x * positiveTwist K sigma (rootLinePositive K k x) ∈ S)
    (u : Positive K) (hfixed : positiveTwist K sigma u = u) : u ∈ S := by
  exact CFSGFiniteFixedFiltration.fixed_mem_of_positive_step
    (positiveTwist K sigma) S (TailInPositive K) (rootHeightBound CartanMatrix.E₆)
    (first_tail_eq_top K) (terminal_tail_eq_bot K)
    (exists_subgroup_height_factor K sigma S hSfixed hsingle hpair) u hfixed

theorem fixed_subgroup_eq_of_root_sections (K : Type) [Field K] [Finite K]
    (sigma : K ≃+* K) (S : Subgroup (Positive K))
    (hSfixed : ∀ a ∈ S, positiveTwist K sigma a = a)
    (hsingle : ∀ (k : PositiveRoot), diagramRoot k.val = k.val → ∀ x : RootLine K k.val,
      unitTwist K sigma x.val = x.val → rootLinePositive K k x ∈ S)
    (hpair : ∀ (k : PositiveRoot), diagramRoot k.val ≠ k.val → ∀ x : RootLine K k.val,
      rootLinePositive K k x * positiveTwist K sigma (rootLinePositive K k x) ∈ S) :
    (positiveTwist K sigma).toMonoidHom.eqLocus (MonoidHom.id (Positive K)) = S := by
  apply le_antisymm
  · intro u hu
    exact fixed_mem_of_root_sections K sigma S hSfixed hsingle hpair u hu
  · exact hSfixed

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedHeightGeneration
