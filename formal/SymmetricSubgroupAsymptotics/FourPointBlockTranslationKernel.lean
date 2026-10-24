import SymmetricSubgroupAsymptotics.FourPointBlockAffineCoordinates
import SymmetricSubgroupAsymptotics.OriginalKernelModuleCoordinateEmbedding
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart

/-! The actual four-point block translation kernel is an elementary
binary group with its literal linear-image action. This constructs its
module and injective coordinates; no splitting or kernel-module premise
is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FourPointBlockTranslationKernel
open FourPointBlockAffineCoordinates BinaryPlanePermutationAffineEquiv
open BinaryPlaneWreathIrreducible SemidirectProduct

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

abbrev kernel : Subgroup G := (projection b hb x₀ hfour).ker

omit [Finite G] [Finite X] in
private theorem kernel_right (u : kernel b hb x₀ hfour) :
    (affineEmbedding b hb x₀ hfour (u : G)).right = 1 :=
  congrArg Subtype.val u.property

/-- Actual translations retained from the faithful original affine embedding. -/
def coordinate : kernel b hb x₀ hfour →* Multiplicative (X → Plane) where
  toFun u := Multiplicative.ofAdd (fun i =>
    ((affineEmbedding b hb x₀ hfour (u : G)).left i).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    change ((affineEmbedding b hb x₀ hfour (1 : G)).left i).toAdd = 0
    rw [map_one]
    rfl
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext i
    change ((affineEmbedding b hb x₀ hfour ((u : G)*(v : G))).left i).toAdd = _
    rw [map_mul]
    change (((affineEmbedding b hb x₀ hfour (u : G)).left *
      BinaryPlaneWreathIrreducible.action
        (affineEmbedding b hb x₀ hfour (u : G)).right
        (affineEmbedding b hb x₀ hfour (v : G)).left) i).toAdd = _
    rw [kernel_right,map_one]
    rfl

theorem coordinate_injective : Function.Injective (coordinate b hb x₀ hfour) := by
  intro u v h
  apply Subtype.ext
  apply affineEmbedding_injective b hb x₀ hfour
  apply SemidirectProduct.ext
  · funext i
    exact Multiplicative.toAdd.injective
      (congrFun (congrArg Multiplicative.toAdd h) i)
  · rw [kernel_right,kernel_right]

/-- Exponent two follows from actual binary translation coordinates. -/
theorem kernel_square (u : kernel b hb x₀ hfour) : u^2 = 1 := by
  apply coordinate_injective b hb x₀ hfour
  rw [map_pow,map_one,pow_two]
  apply Multiplicative.toAdd.injective
  funext i
  change (coordinate b hb x₀ hfour u).toAdd i +
    (coordinate b hb x₀ hfour u).toAdd i = 0
  exact binaryVector_add_self _

omit [Finite G] [Finite X] [MulAction.IsPretransitive G X] in
private theorem conjugate_translation (g : Affine (G := G) (X := X))
    (v : X → Multiplicative Plane) :
    g * inl v * g⁻¹ = inl (BinaryPlaneWreathIrreducible.action g.right v) := by
  conv_lhs => rw [←inl_left_mul_inr_right g]
  have h : (inr g.right : Affine (G := G) (X := X)) * inl v * (inr g.right)⁻¹ =
      inl (BinaryPlaneWreathIrreducible.action g.right v) := by
    rw [←map_inv]
    exact (inl_aut _ _).symm
  calc
    (inl g.left * inr g.right : Affine (G := G) (X := X)) * inl v *
        (inl g.left * inr g.right)⁻¹ =
      (inl g.left : Affine (G := G) (X := X)) *
        ((inr g.right : Affine (G := G) (X := X)) * inl v * (inr g.right)⁻¹) *
          (inl g.left)⁻¹ := by group
    _ = (inl (g.left * BinaryPlaneWreathIrreducible.action g.right v * g.left⁻¹) :
        Affine (G := G) (X := X)) := by
      rw [h,←map_inv,←map_mul,←map_mul]
    _ = _ := by rw [mul_comm g.left,mul_inv_cancel_right]

/-- Conjugation is precisely the displayed original linear-image action. -/
theorem coordinate_conjugation (g : G) (u : kernel b hb x₀ hfour) :
    coordinate b hb x₀ hfour (MulAut.conjNormal g u) =
      Multiplicative.ofAdd
        (BinaryPlaneCyclicWreathUniform.representation (linearImage b hb x₀ hfour)
          (projection b hb x₀ hfour g) (coordinate b hb x₀ hfour u).toAdd) := by
  have hu : affineEmbedding b hb x₀ hfour (u : G) =
      inl (affineEmbedding b hb x₀ hfour (u : G)).left := by
    apply SemidirectProduct.ext
    · rfl
    · exact kernel_right b hb x₀ hfour u
  have he : affineEmbedding b hb x₀ hfour ((MulAut.conjNormal g u : kernel b hb x₀ hfour) : G) =
      inl (BinaryPlaneWreathIrreducible.action
        (affineEmbedding b hb x₀ hfour g).right
        (affineEmbedding b hb x₀ hfour (u : G)).left) := by
    change affineEmbedding b hb x₀ hfour (g*(u : G)*g⁻¹) = _
    rw [map_mul,map_mul,map_inv,hu,conjugate_translation]
    rfl
  apply Multiplicative.toAdd.injective
  funext i
  exact congrArg (fun z : Affine (G := G) (X := X) => (z.left i).toAdd) he

/-- Intrinsic kernel module on the actual original linear image. -/
abbrev kernelModule : Rep (ZMod 2) (linearImage b hb x₀ hfour) :=
  ElementaryBinaryKernelOriginalChart.kernelModule (projection b hb x₀ hfour)
    (projection_surjective b hb x₀ hfour) (kernel_square b hb x₀ hfour)

def kernelModuleChart : OriginalKernelModuleChart (projection b hb x₀ hfour)
    (kernelModule b hb x₀ hfour) :=
  ElementaryBinaryKernelOriginalChart.originalChart (projection b hb x₀ hfour)
    (projection_surjective b hb x₀ hfour) (kernel_square b hb x₀ hfour)

/-- Injective intertwiner from the exact correlated kernel to the full
binary-plane block module, constructed from actual translation coordinates. -/
def kernelInclusion : Representation.IntertwiningMap (kernelModule b hb x₀ hfour).ρ
    (BinaryPlaneCyclicWreathUniform.representation (linearImage b hb x₀ hfour)) := by
  let rho := BinaryPlaneCyclicWreathUniform.representation (linearImage b hb x₀ hfour)
  let A := Rep.of rho
  let pi := projection b hb x₀ hfour
  let r : linearImage b hb x₀ hfour → G := fun h =>
    Classical.choose (projection_surjective b hb x₀ hfour h)
  have hr (h) : pi (r h) = h := Classical.choose_spec (projection_surjective b hb x₀ hfour h)
  apply (kernelModuleChart b hb x₀ hfour).coordinateIntertwiner pi
    (kernelModule b hb x₀ hfour) A (coordinate b hb x₀ hfour) r hr
  intro h u
  have hc := coordinate_conjugation b hb x₀ hfour (r h) u
  change coordinate b hb x₀ hfour (MulAut.conjNormal (r h) u) =
    Multiplicative.ofAdd (rho (pi (r h)) (coordinate b hb x₀ hfour u).toAdd) at hc
  rw [hr] at hc
  exact hc

theorem kernelInclusion_injective : Function.Injective (kernelInclusion b hb x₀ hfour) := by
  unfold kernelInclusion
  exact (kernelModuleChart b hb x₀ hfour).coordinateLinear_injective
    (projection b hb x₀ hfour) (kernelModule b hb x₀ hfour)
    (Rep.of (BinaryPlaneCyclicWreathUniform.representation (linearImage b hb x₀ hfour)))
    (coordinate b hb x₀ hfour) (coordinate_injective b hb x₀ hfour)

end SymmetricSubgroupAsymptotics.FourPointBlockTranslationKernel
