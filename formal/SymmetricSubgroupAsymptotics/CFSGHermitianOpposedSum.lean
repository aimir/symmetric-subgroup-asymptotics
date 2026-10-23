import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedPieceMultiplier
import Mathlib.LinearAlgebra.Prod

/-! Exact cross-pairing on two singular spaces determines an isometry
on their whole sum. Nondegeneracy and injectivity of the image are
proved from the original opposed pairing, not supplied for the image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOpposedSum
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)
variable (P Z : Submodule K (I → K))

def sourceSum : (P × Z) →ₗ[K] (I → K) := P.subtype.coprod Z.subtype

def imageSum (a : P →ₗ[K] (I → K)) (b : Z →ₗ[K] (I → K)) :
    (P × Z) →ₗ[K] (I → K) := a.coprod b

theorem sum_pair (a : P →ₗ[K] (I → K)) (b : Z →ₗ[K] (I → K))
    (hP : Orthogonal sigma H P P) (hZ : Orthogonal sigma H Z Z)
    (ha : ∀ x y : P, hermitianPair sigma H (a x) (a y) = 0)
    (hb : ∀ x y : Z, hermitianPair sigma H (b x) (b y) = 0)
    (hcross : ∀ x : P, ∀ y : Z,
      hermitianPair sigma H (a x) (b y) = hermitianPair sigma H x.val y.val)
    (delta : K)
    (hflip : ∀ x y, hermitianPair sigma H y x = delta * sigma (hermitianPair sigma H x y))
    (v w : P × Z) :
    hermitianPair sigma H (imageSum P Z a b v) (imageSum P Z a b w) =
      hermitianPair sigma H (sourceSum P Z v) (sourceSum P Z w) := by
  have hreverse (x : Z) (y : P) :
      hermitianPair sigma H (b x) (a y) = hermitianPair sigma H x.val y.val := by
    rw [hflip, hcross, ← hflip]
  change hermitianPair sigma H (a v.1 + b v.2) (a w.1 + b w.2) =
    hermitianPair sigma H (v.1.val + v.2.val) (w.1.val + w.2.val)
  rw [hermitianPair_add_left,hermitianPair_add_left,
    hermitianPair_add_right,hermitianPair_add_right,
    hermitianPair_add_right,hermitianPair_add_right,
    ha,hb,hcross,hreverse,hP _ v.1.property _ w.1.property,
    hZ _ v.2.property _ w.2.property]

theorem source_nondegenerate (hP : Orthogonal sigma H P P) (hZ : Orthogonal sigma H Z Z)
    (hPZ : ∀ x ∈ P, (∀ y ∈ Z, hermitianPair sigma H x y = 0) → x = 0)
    (hZP : ∀ y ∈ Z, (∀ x ∈ P, hermitianPair sigma H y x = 0) → y = 0)
    (v : P × Z)
    (hv : ∀ w : P × Z, hermitianPair sigma H (sourceSum P Z v) (sourceSum P Z w) = 0) :
    v = 0 := by
  have hx : v.1.val = 0 := by
    apply hPZ _ v.1.property
    intro z hz
    have hh := hv (0,⟨z,hz⟩)
    change hermitianPair sigma H (v.1.val + v.2.val) (0 + z) = 0 at hh
    rw [zero_add,hermitianPair_add_left,hZ _ v.2.property z hz,add_zero] at hh
    exact hh
  have hy : v.2.val = 0 := by
    apply hZP _ v.2.property
    intro p hp
    have hh := hv (⟨p,hp⟩,0)
    change hermitianPair sigma H (v.1.val + v.2.val) (p + 0) = 0 at hh
    rw [hx,zero_add,add_zero] at hh
    exact hh
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

theorem sourceSum_injective (hP : Orthogonal sigma H P P) (hZ : Orthogonal sigma H Z Z)
    (hPZ : ∀ x ∈ P, (∀ y ∈ Z, hermitianPair sigma H x y = 0) → x = 0)
    (hZP : ∀ y ∈ Z, (∀ x ∈ P, hermitianPair sigma H y x = 0) → y = 0) :
    Function.Injective (sourceSum P Z) := by
  intro v w he
  apply sub_eq_zero.mp
  apply source_nondegenerate sigma H P Z hP hZ hPZ hZP
  intro t
  have hh : sourceSum P Z (v-w) = 0 := by rw [map_sub,he,sub_self]
  rw [hh,pair_zero_left]

theorem imageSum_injective (a : P →ₗ[K] (I → K)) (b : Z →ₗ[K] (I → K))
    (hP : Orthogonal sigma H P P) (hZ : Orthogonal sigma H Z Z)
    (hPZ : ∀ x ∈ P, (∀ y ∈ Z, hermitianPair sigma H x y = 0) → x = 0)
    (hZP : ∀ y ∈ Z, (∀ x ∈ P, hermitianPair sigma H y x = 0) → y = 0)
    (hpair : ∀ v w : P × Z,
      hermitianPair sigma H (imageSum P Z a b v) (imageSum P Z a b w) =
        hermitianPair sigma H (sourceSum P Z v) (sourceSum P Z w)) :
    Function.Injective (imageSum P Z a b) := by
  intro v w he
  apply sub_eq_zero.mp
  apply source_nondegenerate sigma H P Z hP hZ hPZ hZP
  intro t
  have hh : imageSum P Z a b (v-w) = 0 := by rw [map_sub,he,sub_self]
  rw [← hpair,hh,pair_zero_left]

theorem imageSum_range_nondegenerate (a : P →ₗ[K] (I → K)) (b : Z →ₗ[K] (I → K))
    (hP : Orthogonal sigma H P P) (hZ : Orthogonal sigma H Z Z)
    (hPZ : ∀ x ∈ P, (∀ y ∈ Z, hermitianPair sigma H x y = 0) → x = 0)
    (hZP : ∀ y ∈ Z, (∀ x ∈ P, hermitianPair sigma H y x = 0) → y = 0)
    (hpair : ∀ v w : P × Z,
      hermitianPair sigma H (imageSum P Z a b v) (imageSum P Z a b w) =
        hermitianPair sigma H (sourceSum P Z v) (sourceSum P Z w)) :
    ∀ x ∈ (imageSum P Z a b).range,
      (∀ y ∈ (imageSum P Z a b).range, hermitianPair sigma H x y = 0) → x = 0 := by
  rintro x ⟨v,rfl⟩ hv
  have he : v = 0 := source_nondegenerate sigma H P Z hP hZ hPZ hZP v (by
    intro w
    rw [← hpair]
    exact hv _ ⟨w,rfl⟩)
  rw [he,map_zero]

end SymmetricSubgroupAsymptotics.CFSGHermitianOpposedSum
