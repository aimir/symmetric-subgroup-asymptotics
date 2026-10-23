import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Field.Defs

/-! Disjoint spaces containing the two hyperbolic axes have disjoint
tails when their opposite heads vanish. Subtracting the actual head
axis gives the SAME tail representative in both spaces. This is linear
algebra on the literal pole coordinates, without an orthogonal premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicTailDisjoint
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

def tailMap : (K × (W × K)) →ₗ[K] W where
  toFun x := x.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem disjoint_tails (P R : Submodule K (K × (W × K)))
    (hdis : Disjoint P R) (he : (1, ((0 : W), (0 : K))) ∈ P)
    (hf : (0, ((0 : W), (1 : K))) ∈ R)
    (hP : ∀ x ∈ P, x.2.2 = 0) (hR : ∀ x ∈ R, x.1 = 0) :
    Disjoint (Submodule.map (tailMap (K := K) (W := W)) P)
      (Submodule.map (tailMap (K := K) (W := W)) R) := by
  apply Submodule.disjoint_def.mpr
  intro z hzP hzR
  obtain ⟨p, hp, hpt⟩ := hzP
  obtain ⟨r, hr, hrt⟩ := hzR
  have hpz : p - p.1 • (1, ((0 : W), (0 : K))) = (0, (z, 0)) := by
    apply Prod.ext
    · change p.1 - p.1 * 1 = 0
      rw [mul_one, sub_self]
    · apply Prod.ext
      · change p.2.1 - p.1 • (0 : W) = z
        simpa only [smul_zero, sub_zero] using hpt
      · change p.2.2 - p.1 * 0 = 0
        rw [mul_zero, sub_zero, hP p hp]
  have hrz : r - r.2.2 • (0, ((0 : W), (1 : K))) = (0, (z, 0)) := by
    apply Prod.ext
    · change r.1 - r.2.2 * 0 = 0
      rw [mul_zero, sub_zero, hR r hr]
    · apply Prod.ext
      · change r.2.1 - r.2.2 • (0 : W) = z
        simpa only [smul_zero, sub_zero] using hrt
      · change r.2.2 - r.2.2 * 1 = 0
        rw [mul_one, sub_self]
  have hzp : (0, (z, (0 : K))) ∈ P := hpz ▸ P.sub_mem hp (P.smul_mem p.1 he)
  have hzr : (0, (z, (0 : K))) ∈ R := hrz ▸ R.sub_mem hr (R.smul_mem r.2.2 hf)
  exact congrArg (fun x : K × (W × K) => x.2.1)
    ((Submodule.disjoint_def.mp hdis) (0, (z, 0)) hzp hzr)

end SymmetricSubgroupAsymptotics.CFSGHyperbolicTailDisjoint
