import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHeightClassLifting

/-! Genuine fixed-height peeling: remove the displayed fixed section
product and retain an actually fixed element of the next height tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHeightPeeling
open CFSGTrialityGeckFixedHeightClassLifting CFSGTrialityGeckWordHeightCoordinates
open CFSGTrialityGeckWordCoordinateTwist CFSGTrialityGeckWordRootIndex
open CFSGTrialityGeckHeightCoordinateAction CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityGeckPositiveTwist CFSGNormTwoCoordinateRootHeightFiltration
open CFSGTrialityD4NormTwo

private abbrev PeelPositive (K : Type) [Field K] :=
  CFSGNormTwoCoordinateRootHeightQuotient.PositiveGroup (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K

private theorem fixed_kernel_remainder {G Q : Type*} [Group G] [Group Q]
    (q : G →* Q) (F : MulAut G) (u p : G)
    (hu : F u = u) (hp : F p = p) (he : q p = q u) :
    p⁻¹*u ∈ q.ker ∧ F (p⁻¹*u) = p⁻¹*u ∧ u = p*(p⁻¹*u) := by
  refine ⟨?_,?_,(mul_inv_cancel_left p u).symm⟩
  · change q (p⁻¹*u) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  · rw [map_mul,map_inv,hp,hu]

local instance peelTailNormal (K : Type) [Field K] (h : ℤ) :
    (TailInPositive K h).Normal :=
  heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h

theorem exists_fixed_height_factor (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (hh : 0 < h) (u : PeelPositive K) (hu : u ∈ TailInPositive K h)
    (hfix : positiveTwist K σ u = u) :
    ∃ c : WordHeightIndex h → Multiplicative K,coordinateTwist K σ h c = c ∧
      ∃ v : PeelPositive K,v ∈ TailInPositive K (h + 1) ∧ positiveTwist K σ v = v ∧
        u = (sectionRepresentative K σ h c).val * v := by
  let q : PeelPositive K →* Quotient K h := QuotientGroup.mk' (TailInPositive K (h + 1))
  let x : HeightImage K h := ⟨q u,⟨u,hu,rfl⟩⟩
  have hx : heightImageTwist K σ h x = x := by
    apply Subtype.ext
    change quotientTwist K σ h (QuotientGroup.mk' (TailInPositive K (h + 1)) u) =
      QuotientGroup.mk' (TailInPositive K (h + 1)) u
    rw [quotientTwist_mk,hfix]
  let c := (wordHeightLayerEquiv K h hh).symm x
  have he : wordHeightLayerEquiv K h hh c = x :=
    (wordHeightLayerEquiv K h hh).apply_symm_apply x
  have hc : coordinateTwist K σ h c = c :=
    (fixed_iff_coordinates K σ h hh c).mp (by rw [he]; exact hx)
  let p : PeelPositive K := (sectionRepresentative K σ h c).val
  have hp : q p = q u := by
    have hi := congrArg Subtype.val (sectionRepresentative_image K σ h hh c hc)
    exact hi.trans (congrArg Subtype.val he)
  have hpf : positiveTwist K σ p = p := sectionRepresentative_fixed K σ h c hc
  let F : MulAut (PeelPositive K) := positiveTwist K σ
  have hr := fixed_kernel_remainder q F u p hfix hpf hp
  have hv : p⁻¹*u ∈ TailInPositive K (h + 1) := by
    have hk := hr.1
    change p⁻¹*u ∈ (QuotientGroup.mk' (TailInPositive K (h + 1))).ker at hk
    rw [QuotientGroup.ker_mk'] at hk
    exact hk
  exact ⟨c,hc,p⁻¹*u,hv,hr.2.1,hr.2.2⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHeightPeeling
