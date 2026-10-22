import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm

/-! A faithful linear group with an actual permutation of coordinate blocks
has the usual wreath-product order divisor.  Only the kernel has to preserve
coordinate kernels.  The coordinate representations and their joint faithful
action are constructed here; a wreath embedding or a cardinal bound is not
an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGLinearBlockKernelOrderBudget

variable {k G I W : Type*} [Field k] [Group G] [DecidableEq I]
    [AddCommGroup W] [Module k W]

variable (rho : Representation k G (I → W))
    (hzero : ∀ (g : G) (v : I → W) (i : I), v i = 0 → rho g v i = 0)

include hzero in
theorem apply_coordinate (g : G) (v : I → W) (i : I) :
    rho g v i = rho g (Pi.single i (v i)) i := by
  have hh := hzero g (v - Pi.single i (v i)) i (by simp)
  simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using hh

/-- The action induced on a single block, obtained from its literal coordinate
projection rather than from a chosen isomorphic group. -/
def coordinateRepresentation (i : I) : Representation k G W where
  toFun g := (LinearMap.proj i).comp ((rho g).comp (LinearMap.single k _ i))
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    change rho (g*h) (Pi.single i w) i =
      rho g (Pi.single i (rho h (Pi.single i w) i)) i
    rw [map_mul]
    exact apply_coordinate rho hzero g (rho h (Pi.single i w)) i

/-- The product of the actual block actions. -/
def coordinateHom : G →* (I → W ≃ₗ[k] W) where
  toFun g i := LinearMap.GeneralLinearGroup.generalLinearEquiv k W
    ((coordinateRepresentation rho hzero i).asGroupHom g)
  map_one' := by
    funext i
    simp
  map_mul' g h := by
    funext i
    simp

theorem coordinateHom_injective (hfaithful : Function.Injective rho) :
    Function.Injective (coordinateHom rho hzero) := by
  intro g h hgh
  apply hfaithful
  ext v i
  rw [apply_coordinate rho hzero g v i, apply_coordinate rho hzero h v i]
  exact congrArg (fun f : W ≃ₗ[k] W => f (v i)) (congrFun hgh i)

include hzero in
theorem card_dvd_block_power [Finite G] [Fintype I] [Finite W]
    (hfaithful : Function.Injective rho) :
    Nat.card G ∣ Nat.card (W ≃ₗ[k] W) ^ Fintype.card I := by
  have hh := Subgroup.card_dvd_of_injective (coordinateHom rho hzero)
    (coordinateHom_injective rho hzero hfaithful)
  simpa only [Nat.card_pi, Finset.prod_const, Finset.card_univ] using hh

/-- A genuine permutation of blocks charges a single factorial, while its
kernel acts faithfully through the coordinate representations just built. -/
theorem card_dvd_block_power_mul_factorial [Finite G] [Fintype I] [Finite W]
    (hfaithful : Function.Injective rho) (pi : G →* Equiv.Perm I)
    (hker : ∀ (g : pi.ker) (v : I → W) (i : I),
      v i = 0 → rho g.val v i = 0) :
    Nat.card G ∣ Nat.card (W ≃ₗ[k] W) ^ Fintype.card I * Nat.factorial (Fintype.card I) := by
  have hk : Nat.card pi.ker ∣ Nat.card (W ≃ₗ[k] W) ^ Fintype.card I :=
    card_dvd_block_power (rho.comp pi.ker.subtype) hker
      (hfaithful.comp Subtype.val_injective)
  have hr : Nat.card pi.range ∣ Nat.factorial (Fintype.card I) := by
    have hh := Subgroup.card_subgroup_dvd_card pi.range
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm I), Fintype.card_perm] at hh
    exact hh
  have hc : Nat.card G = Nat.card pi.ker * Nat.card pi.range := by
    rw [← Subgroup.index_ker pi]
    exact pi.ker.card_mul_index.symm
  rw [hc]
  exact Nat.mul_dvd_mul hk hr

section Chart
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The representation on the original vector space is transported through
the specified block chart, with no replacement of its acting group. -/
def chartRepresentation (sigma : Representation k G V) (e : V ≃ₗ[k] (I → W)) :
    Representation k G (I → W) :=
  (LinearEquiv.conjRingEquiv e).toMonoidHom.comp sigma

theorem chartRepresentation_apply (sigma : Representation k G V)
    (e : V ≃ₗ[k] (I → W)) (g : G) (v : I → W) :
    chartRepresentation sigma e g v = e (sigma g (e.symm v)) := rfl

theorem card_dvd_of_block_chart [Finite G] [Fintype I] [Finite W]
    (sigma : Representation k G V) (hsigma : Function.Injective sigma)
    (e : V ≃ₗ[k] (I → W)) (pi : G →* Equiv.Perm I)
    (hker : ∀ (g : pi.ker) (v : V) (i : I),
      e v i = 0 → e (sigma g.val v) i = 0) :
    Nat.card G ∣ Nat.card (W ≃ₗ[k] W) ^ Fintype.card I *
      Nat.factorial (Fintype.card I) := by
  apply card_dvd_block_power_mul_factorial (chartRepresentation sigma e)
    ((LinearEquiv.conjRingEquiv e).injective.comp hsigma) pi
  intro g v i hi
  apply hker g (e.symm v) i
  simpa only [e.apply_symm_apply] using hi

end Chart

end SymmetricSubgroupAsymptotics.CFSGLinearBlockKernelOrderBudget
