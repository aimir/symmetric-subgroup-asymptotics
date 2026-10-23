import SymmetricSubgroupAsymptotics.CFSGHermitianLineIsometry
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSumEquiv

/-! Extend a concrete pairing-preserving map on a nondegenerate
codimension-one subspace. Its image complement is derived from the
literal pairing; the remaining line is matched using norm surjectivity.
Every ambient equivalence in the conclusion is explicitly constructed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianCodimensionOneExtension
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
open CFSGFiniteHermitianNondegenerateComplement
variable {K I : Type*} [Field K] [Finite K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

omit [Finite K] in
theorem isometry_injective (W : Submodule K (I → K)) (a : W →ₗ[K] (I → K))
    (hW : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hpair : ∀ x y : W, hermitianPair sigma H (a x) (a y) = hermitianPair sigma H x.val y.val) :
    Function.Injective a := by
  intro x y he
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply hW _ (x-y).property
  intro z hz
  have hh := hpair (x-y) ⟨z,hz⟩
  have ha : a (x-y) = 0 := by rw [map_sub,he,sub_self]
  rw [ha,pair_zero_left] at hh
  exact hh.symm

omit [Finite K] in
theorem range_nondegenerate (W : Submodule K (I → K)) (a : W →ₗ[K] (I → K))
    (hW : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hpair : ∀ x y : W, hermitianPair sigma H (a x) (a y) = hermitianPair sigma H x.val y.val) :
    ∀ x ∈ a.range, (∀ y ∈ a.range, hermitianPair sigma H x y = 0) → x = 0 := by
  rintro x ⟨w,rfl⟩ hw
  have hw0 : w.val = 0 := hW _ w.property (by
    intro z hz
    rw [← hpair w ⟨z,hz⟩]
    exact hw _ ⟨⟨z,hz⟩,rfl⟩)
  have he : w = 0 := Subtype.ext hw0
  rw [he,map_zero]

theorem rightPerp_nondegenerate (W : Submodule K (I → K))
    (hW : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hND : ∀ x, (∀ y, hermitianPair sigma H x y = 0) → x = 0)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0) :
    ∀ x ∈ rightPerp sigma H W,
      (∀ y ∈ rightPerp sigma H W, hermitianPair sigma H x y = 0) → x = 0 := by
  intro x hx hzero
  apply hND
  intro z
  have hz : z ∈ W ⊔ rightPerp sigma H W := by
    rw [(isCompl_rightPerp sigma H W hW hswap).sup_eq_top]
    trivial
  obtain ⟨w,hw,c,hc,he⟩ := Submodule.mem_sup.mp hz
  rw [← he,hermitianPair_add_right,(hswap w x).mp (hx w hw),hzero c hc,zero_add]

theorem exists_extension (W : Submodule K (I → K)) (a : W →ₗ[K] (I → K))
    (hW : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y = 0) → x = 0)
    (hND : ∀ x, (∀ y, hermitianPair sigma H x y = 0) → x = 0)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (hpair : ∀ x y : W, hermitianPair sigma H (a x) (a y) = hermitianPair sigma H x.val y.val)
    (hdim : Module.finrank K W + 1 = Fintype.card I)
    (hfixed : ∀ x, sigma (hermitianPair sigma H x x) = hermitianPair sigma H x x)
    (hnorm : ∀ t : K, t ≠ 0 → sigma t = t → ∃ c : K, sigma c * c = t) :
    ∃ e : (I → K) ≃ₗ[K] (I → K),
      (∀ x y, hermitianPair sigma H (e x) (e y) = hermitianPair sigma H x y) ∧
      ∀ w : W, e w.val = a w := by
  let C := rightPerp sigma H W
  let T := a.range
  let D := rightPerp sigma H T
  have hT : ∀ x ∈ T, (∀ y ∈ T, hermitianPair sigma H x y = 0) → x = 0 :=
    range_nondegenerate sigma H W a hW hpair
  have hWC : IsCompl W C := isCompl_rightPerp sigma H W hW hswap
  have hTD : IsCompl T D := isCompl_rightPerp sigma H T hT hswap
  let eW : W ≃ₗ[K] T := LinearEquiv.ofInjective a (isometry_injective sigma H W a hW hpair)
  have hCdim : Module.finrank K C = 1 := by
    have hh := finrank_add_rightPerp sigma H W hW hswap
    change Module.finrank K W + Module.finrank K C = Fintype.card I at hh
    omega
  have hDdim : Module.finrank K D = 1 := by
    have hh := finrank_add_rightPerp sigma H T hT hswap
    have he : Module.finrank K W = Module.finrank K T := eW.finrank_eq
    change Module.finrank K T + Module.finrank K D = Fintype.card I at hh
    omega
  obtain ⟨eC,heC⟩ := CFSGHermitianLineIsometry.exists_isometry sigma H C D hCdim hDdim
    (rightPerp_nondegenerate sigma H W hW hND hswap)
    (rightPerp_nondegenerate sigma H T hT hND hswap) hfixed hnorm
  let e := CFSGHermitianOrthogonalSumEquiv.sumEquiv W C T D hWC hTD eW eC
  refine ⟨e,?_,?_⟩
  · exact CFSGHermitianOrthogonalSumEquiv.sumEquiv_pair sigma H W C T D hWC hTD eW eC
      hpair heC (fun _ hx _ hy => hy _ hx)
      (fun x hx y hy => (hswap y x).mp (hx y hy))
      (fun _ hx _ hy => hy _ hx)
      (fun x hx y hy => (hswap y x).mp (hx y hy))
  · intro w
    exact CFSGHermitianOrthogonalSumEquiv.sumEquiv_apply_left W C T D hWC hTD eW eC w

end SymmetricSubgroupAsymptotics.CFSGHermitianCodimensionOneExtension
