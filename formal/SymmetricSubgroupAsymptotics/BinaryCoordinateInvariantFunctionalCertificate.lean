import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead

/-! A selected coordinate certificate can bound the full invariant-form
head of an actual binary submodule. It checks only its coordinate linear
functionals and literal generator equations; no group table is built. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
namespace BinaryCoordinateInvariantFunctionalCertificate
variable {G : Type} [Group G] {w d n : ℕ}
    (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
    (generators : Fin n → G) (C : BinaryCoordinateSpace w d)

def Compatible (t : Fin d → ZMod 2) : Prop :=
  ∀ (g : Fin n) (j : Fin d),
    ∑ i : Fin d, C.coordinates (rho (generators g) (C.inclusion (Pi.single j 1))) i * t i = t j

variable (W : Subrepresentation rho) (hW : W.toSubmodule = C.space)
private def stateEquiv : (Fin d → ZMod 2) ≃ₗ[ZMod 2] W.toSubmodule :=
  C.equiv.trans (LinearEquiv.ofEq _ _ hW.symm)

private theorem linear_form_expansion
    (ell : W.toSubmodule →ₗ[ZMod 2] ZMod 2) (v : Fin d → ZMod 2) :
    ell (stateEquiv rho C W hW v) =
      ∑ i : Fin d, v i * ell (stateEquiv rho C W hW (Pi.single i 1)) := by
  have hv : v = ∑ i : Fin d, v i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]

private def headCoordinates :
    (W.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) →ₗ[ZMod 2]
      (Fin d → ZMod 2) where
  toFun ell i := ell (stateEquiv rho C W hW (Pi.single i 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem headCoordinates_injective : Function.Injective (headCoordinates rho C W hW) := by
  intro a b he
  apply DFunLike.ext
  intro v
  obtain ⟨c, rfl⟩ := (stateEquiv rho C W hW).surjective v
  change a.toLinearMap (stateEquiv rho C W hW c) = b.toLinearMap (stateEquiv rho C W hW c)
  rw [linear_form_expansion rho C W hW a.toLinearMap,
    linear_form_expansion rho C W hW b.toLinearMap]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x : ZMod 2 => c i * x) (congrFun he i)

private theorem headCoordinates_compatible
    (ell : W.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) :
    Compatible rho generators C (headCoordinates rho C W hW ell) := by
  intro g j
  let v := stateEquiv rho C W hW (Pi.single j 1)
  have hcoord : stateEquiv rho C W hW
      (C.coordinates (rho (generators g) (C.inclusion (Pi.single j 1)))) =
      W.toRepresentation (generators g) v := by
    apply Subtype.ext
    apply (C.mem_iff _).mp
    rw [← hW]
    exact W.apply_mem_toSubmodule (generators g) v.property
  have he := linear_form_expansion rho C W hW ell.toLinearMap
    (C.coordinates (rho (generators g) (C.inclusion (Pi.single j 1))))
  rw [hcoord] at he
  have hi := Representation.IntertwiningMap.isIntertwining _ _ ell (generators g) v
  change ell (W.toRepresentation (generators g) v) = ell v at hi
  exact he.symm.trans hi

include hW in
theorem head_finrank_le_one
    (j : Fin d)
    (hcertificate : ∀ t : Fin d → ZMod 2, Compatible rho generators C t → t j = 0 → t = 0) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  let ev : (W.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) →ₗ[ZMod 2]
      ZMod 2 := (LinearMap.proj j).comp (headCoordinates rho C W hW)
  have hev : Function.Injective ev := by
    intro a b he
    have hz : ev (a - b) = 0 := by rw [map_sub, he, sub_self]
    have hc := hcertificate (headCoordinates rho C W hW (a - b))
      (headCoordinates_compatible rho generators C W hW (a - b)) hz
    have hh : headCoordinates rho C W hW (a - b) = headCoordinates rho C W hW 0 := by
      simpa only [map_zero] using hc
    exact sub_eq_zero.mp (headCoordinates_injective rho C W hW hh)
  have hb := ev.finrank_le_finrank_of_injective hev
  rw [representationHead_finrank_eq_coinvariants] at hb
  exact hb.trans (Module.finrank_self (ZMod 2)).le

end BinaryCoordinateInvariantFunctionalCertificate
end SymmetricSubgroupAsymptotics
