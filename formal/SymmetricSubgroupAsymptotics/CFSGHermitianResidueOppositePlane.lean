import SymmetricSubgroupAsymptotics.CFSGHermitianHyperbolicCompression
import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicExtension
import SymmetricSubgroupAsymptotics.CFSGPolarCommonPointPlanes

/-! The literal common-opposite construction in a hyperbolic block:
the last axis plus a singular middle ray is disjoint from any head
space whose compressed residue does not contain that ray. No polar
building, residue census or ambient group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianHyperbolicCompression
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

def lastAxis : Index J → K
  | .inr (.inr _) => 1
  | _ => 0

def residueOppositePlane (v : J → K) : Submodule K (Index J → K) :=
  Submodule.span K {lastAxis, middleVector v}

private theorem orthogonal_two_spans (sigma : K ≃+* K)
    (H : Matrix (Index J) (Index J) K) (u v : Index J → K)
    (h : hermitianPair sigma H u v = 0) : Orthogonal sigma H (K ∙ u) (K ∙ v) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [hermitianPair_smul, h, mul_zero]

theorem residueOppositePlane_pair_zero (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (v : J → K) (hv : hermitianPair sigma H v v = 0) :
    Orthogonal sigma (blockForm eps H) (residueOppositePlane v) (residueOppositePlane v) := by
  have h00 : hermitianPair sigma (blockForm eps H) (lastAxis : Index J → K) lastAxis = 0 := by
    rw [block_pair]
    change sigma 0 * 1 + hermitianPair sigma H 0 0 + eps * sigma 1 * 0 = 0
    rw [map_zero, map_one, pair_zero_left, zero_mul, mul_zero, add_zero, add_zero]
  have h01 : hermitianPair sigma (blockForm eps H) (lastAxis : Index J → K) (middleVector v) = 0 := by
    rw [block_pair]
    change sigma 0 * 0 + hermitianPair sigma H 0 v + eps * sigma 1 * 0 = 0
    rw [map_zero, map_one, pair_zero_left, zero_mul, mul_zero, add_zero, add_zero]
  have h10 : hermitianPair sigma (blockForm eps H) (middleVector v) (lastAxis : Index J → K) = 0 := by
    rw [block_pair]
    change sigma 0 * 1 + hermitianPair sigma H v 0 + eps * sigma 0 * 0 = 0
    rw [map_zero, pair_zero_right, zero_mul, mul_zero, add_zero, add_zero]
  have h11 : hermitianPair sigma (blockForm eps H) (middleVector v) (middleVector v) = 0 := by
    rw [middle_pair]
    exact hv
  rw [residueOppositePlane, Submodule.span_insert,
    orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
  exact ⟨⟨orthogonal_two_spans sigma _ _ _ h00, orthogonal_two_spans sigma _ _ _ h01⟩,
    orthogonal_two_spans sigma _ _ _ h10, orthogonal_two_spans sigma _ _ _ h11⟩

theorem residueOppositePlane_finrank (v : J → K) (hv : v ≠ 0) :
    Module.finrank K (residueOppositePlane v) = 2 := by
  have hlast : (lastAxis : Index J → K) ≠ 0 := by
    intro h
    have hh := congrFun h (.inr (.inr ()))
    exact one_ne_zero hh
  have hnot (a : K) : middleVector v ≠ a • (lastAxis : Index J → K) := by
    intro he
    have hh := congrArg (middleProjection (K := K) (J := J)) he
    rw [middleProjection_middleVector, map_smul] at hh
    change v = a • (0 : J → K) at hh
    exact hv (hh.trans (smul_zero a))
  exact CFSGPolarCommonPointPlanes.pairPlane_finrank _ _ hlast hnot

theorem residueOppositePlane_disjoint (S : Submodule K (Index J → K))
    (hz : ∀ x ∈ S, x (.inr (.inr ())) = 0)
    (v : J → K) (hv : v ∉ compressedSpace S) : Disjoint S (residueOppositePlane v) := by
  apply Submodule.disjoint_def.mpr
  intro x hxS hxR
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxR
  have ha := hz _ hxS
  change a * 1 + b * 0 = 0 at ha
  simp only [mul_one, mul_zero, add_zero] at ha
  subst a
  simp only [zero_smul, zero_add] at hxS ⊢
  by_cases hb : b = 0
  · rw [hb, zero_smul]
  · have hm := S.smul_mem b⁻¹ hxS
    have hvS : middleVector v ∈ S := by
      simpa only [smul_smul, inv_mul_cancel₀ hb, one_smul] using hm
    exact (hv hvS).elim

end SymmetricSubgroupAsymptotics.CFSGHermitianHyperbolicCompression
