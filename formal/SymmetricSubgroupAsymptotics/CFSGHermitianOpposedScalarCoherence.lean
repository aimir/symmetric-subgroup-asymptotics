import SymmetricSubgroupAsymptotics.CFSGHermitianMixedMaximalSpace
import SymmetricSubgroupAsymptotics.CFSGIndependentPairRayRatio
import SymmetricSubgroupAsymptotics.CFSGTwoFunctionalKernelVector

/-! One mixed scalar works across an entire opposed pair of singular
spaces. Genuine common kernels in rank at least three connect every
direction, with reciprocal ratios read from the same actual point map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem hermitian_opposed_common_ratio
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (P Z : IsotropicSpace sigma H)
    (hd : 3 ≤ Module.finrank K P.val) (hdZ : 3 ≤ Module.finrank K Z.val)
    (hdis : Disjoint P.val Z.val)
    (hlinear : ∀ M : MaximalSpace sigma H,
      Nonempty (SemilinearPiece sigma H f ⟨M.val, M.property.1⟩ (RingEquiv.refl K)))
    (hfixP : ∀ R : SingularPoint sigma H, R.val ≤ P.val → f R = R)
    (hfixZ : ∀ R : SingularPoint sigma H, R.val ≤ Z.val → f R = R) :
    ∃ t : K, t ≠ 0 ∧ ∀ (x y : I → K), x ∈ P.val → x ≠ 0 → y ∈ Z.val → y ≠ 0 →
      hermitianPair sigma H y x = 0 → ∀ (hxy0 : x + y ≠ 0)
        (hz : hermitianPair sigma H (x + y) (x + y) = 0),
      (f (singularRay sigma H (x + y) hxy0 hz)).val = K ∙ (x + t • y) := by
  have hnotP (y : I → K) (hy : y ∈ Z.val) (hy0 : y ≠ 0) : y ∉ P.val := by
    intro hp
    have hi : y ∈ (P.val ⊓ Z.val : Submodule K (I → K)) := ⟨hp, hy⟩
    rw [hdis.eq_bot] at hi
    exact hy0 hi
  have hnotZ (x : I → K) (hx : x ∈ P.val) (hx0 : x ≠ 0) : x ∉ Z.val := by
    intro hz
    have hi : x ∈ (P.val ⊓ Z.val : Submodule K (I → K)) := ⟨hx, hz⟩
    rw [hdis.eq_bot] at hi
    exact hx0 hi
  let X := {x : P.val // x ≠ 0}
  let Y := {y : Z.val // y ≠ 0}
  have hX (x : X) : x.val.val ≠ 0 := fun h => x.property (Subtype.ext h)
  have hY (y : Y) : y.val.val ≠ 0 := fun h => y.property (Subtype.ext h)
  have hright (y : Y) := exists_hermitian_mixed_ray_ratio sigma H hswap f P hd hlinear y.val.val
    (Z.property _ y.val.property _ y.val.property) (hnotP _ y.val.property (hY y)) hfixP
    (fun R hR => hfixZ R (hR.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr y.val.property)))
  have hleft (x : X) := exists_hermitian_mixed_ray_ratio sigma H hswap f Z hdZ hlinear x.val.val
    (P.property _ x.val.property _ x.val.property) (hnotZ _ x.val.property (hX x)) hfixZ
    (fun R hR => hfixP R (hR.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr x.val.property)))
  choose t ht htr using hright
  choose u hu hur using hleft
  have hproduct (x : X) (y : Y) (hxy : hermitianPair sigma H y.val.val x.val.val = 0) :
      t y * u x = 1 := by
    have hsum0 : x.val.val + y.val.val ≠ 0 := by
      intro hz
      have hyneg : y.val.val = -x.val.val := by rw [add_eq_zero_iff_eq_neg.mp hz, neg_neg]
      exact hnotP _ y.val.property (hY y) (hyneg ▸ P.val.neg_mem x.val.property)
    have hsum0' : y.val.val + x.val.val ≠ 0 := by simpa only [add_comm] using hsum0
    have hxy' := (hswap _ _).mp hxy
    have hsum : hermitianPair sigma H (x.val.val + y.val.val) (x.val.val + y.val.val) = 0 := by
      rw [hermitianPair_add_left, hermitianPair_add_right, hermitianPair_add_right,
        P.property _ x.val.property _ x.val.property, Z.property _ y.val.property _ y.val.property,
        hxy, hxy']
      simp only [add_zero]
    have hsum' : hermitianPair sigma H (y.val.val + x.val.val) (y.val.val + x.val.val) = 0 := by
      simpa only [add_comm] using hsum
    have hrep : singularRay sigma H (y.val.val + x.val.val) hsum0' hsum' =
        singularRay sigma H (x.val.val + y.val.val) hsum0 hsum := by
      apply Subtype.ext
      change K ∙ (y.val.val + x.val.val) = K ∙ (x.val.val + y.val.val)
      rw [add_comm]
    have hR := htr y x.val.val ⟨x.val.property, hxy⟩ hsum0 hsum
    have hL := hur x y.val.val ⟨y.val.property, hxy'⟩ hsum0' hsum'
    have he : K ∙ (x.val.val + t y • y.val.val) = K ∙ (y.val.val + u x • x.val.val) :=
      hR.symm.trans ((congrArg (fun R : SingularPoint sigma H => (f R).val) hrep.symm).trans hL)
    have hli : LinearIndependent K ![x.val.val, y.val.val] :=
      (LinearIndependent.pair_iff' (hX x)).mpr (fun c hc =>
        hnotP _ y.val.property (hY y) (hc ▸ P.val.smul_mem c x.val.property))
    exact CFSGIndependentPairRayRatio.product_eq_one _ _ hli _ _ he
  have hconstant (a b : Y) : t a = t b := by
    obtain ⟨v, hv, hv0, hva, hvb⟩ := CFSGTwoFunctionalKernelVector.exists_nonzero_common_kernel
      P.val hd (pairRightLinear sigma H a.val.val) (pairRightLinear sigma H b.val.val)
    let x : X := ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
    exact mul_right_cancel₀ (hu x) ((hproduct x a hva).trans (hproduct x b hvb).symm)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Z.val)
    (Submodule.one_le_finrank_iff.mp (by omega : 1 ≤ Module.finrank K Z.val))
  let y0 : Y := ⟨⟨y, hy⟩, fun h => hy0 (congrArg Subtype.val h)⟩
  refine ⟨t y0, ht y0, ?_⟩
  intro x y hx hx0 hy hy0 hxy hsum0 hsum
  let y' : Y := ⟨⟨y, hy⟩, fun h => hy0 (congrArg Subtype.val h)⟩
  have he := htr y' x ⟨hx, hxy⟩ hsum0 hsum
  rw [hconstant y' y0] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
