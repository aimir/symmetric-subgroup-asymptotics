import SymmetricSubgroupAsymptotics.CFSGLinearThreeRayPencil
import SymmetricSubgroupAsymptotics.CFSGHermitianSingularRay

/-! Three fixed rays on an actual singular generator line force its
remaining rays fixed when its constructed field component is the identity.
The representative is allowed a larger ambient codomain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

omit [Fintype I] in
private theorem independent_pencil_nonzero (x y : I → K)
    (hxy : LinearIndependent K ![x,y]) (a : K) : x + a • y ≠ 0 := by
  intro he
  have hh := LinearIndependent.pair_iff.mp hxy 1 a (by simpa only [one_smul] using he)
  exact one_ne_zero hh.1

theorem hermitian_three_pencil_rays_fix_base
    (f : Equiv.Perm (SingularPoint sigma H)) (M : IsotropicSpace sigma H)
    (F : SemilinearPiece sigma H f M (RingEquiv.refl K))
    (x y : I → K) (hx : x ∈ M.val) (hy : y ∈ M.val)
    (hxy : LinearIndependent K ![x,y]) (t t' : K) (htt : t ≠ t')
    (hfixY : ∀ R : SingularPoint sigma H, R.val = K ∙ y → f R = R)
    (hfixT : ∀ R : SingularPoint sigma H, R.val = K ∙ (x + t • y) → f R = R)
    (hfixT' : ∀ R : SingularPoint sigma H, R.val = K ∙ (x + t' • y) → f R = R) :
    ∀ R : SingularPoint sigma H, R.val = K ∙ x → f R = R := by
  let xM : M.val := ⟨x, hx⟩
  let yM : M.val := ⟨y, hy⟩
  have hfixed (z : M.val) (hz : z.val ≠ 0)
      (hfix : ∀ R : SingularPoint sigma H, R.val = K ∙ z.val → f R = R) :
      F.map z ∈ K ∙ z.val := by
    have hzM : z ≠ 0 := fun h => hz (congrArg Subtype.val h)
    have hp := F.ray z hzM
    rw [← singularRay_eq_projectiveInside sigma H M z hzM] at hp
    rw [hfix _ rfl] at hp
    change (K ∙ F.map z) = (K ∙ z.val) at hp
    rw [← hp]
    exact Submodule.mem_span_singleton_self (F.map z)
  have hy0 : y ≠ 0 := hxy.ne_zero 1
  have ht0 := independent_pencil_nonzero x y hxy t
  have ht'0 := independent_pencil_nonzero x y hxy t'
  obtain ⟨a, hax, _⟩ := CFSGLinearThreeRayPencil.exists_scalar_of_three_pencil_rays
    M.val.subtype F.map xM yM hxy t t' htt
    (hfixed yM hy0 hfixY)
    (hfixed (xM + t • yM) ht0 hfixT)
    (hfixed (xM + t' • yM) ht'0 hfixT')
  have hax' : F.map xM = a • x := hax
  have hx0 : x ≠ 0 := hxy.ne_zero 0
  have hxM0 : xM ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have ha : a ≠ 0 := by
    intro hz
    have hFzero : F.map xM = 0 := hax'.trans (by rw [hz, zero_smul])
    exact hxM0 (F.injective (hFzero.trans F.map.map_zero.symm))
  intro R hR
  have hp := F.ray xM hxM0
  rw [← singularRay_eq_projectiveInside sigma H M xM hxM0] at hp
  have hRx : R = singularRay sigma H x hx0 (M.property x hx x hx) := Subtype.ext hR
  rw [hRx]
  apply Subtype.ext
  change (f (singularRay sigma H x hx0 (M.property x hx x hx))).val = K ∙ x
  have hspan : (K ∙ F.map xM) = (K ∙ (a • x)) :=
    congrArg (fun v : I → K => K ∙ v) hax'
  exact hp.symm.trans (hspan.trans
    (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) _))

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
