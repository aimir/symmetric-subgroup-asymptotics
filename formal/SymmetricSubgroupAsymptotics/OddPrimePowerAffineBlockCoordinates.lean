import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.FunctionBlockOrbitUniform
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! Actual prime-field translation coordinates in affine blocks of any
prime-power degree. The complement projection belongs to the literal
base component. Its compressed kernel is an actual normal subgroup of
the original group, embedded as its correlated prime-field subspace.
Local linear transports retain arbitrary destination-dependent holonomy. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockCoordinates

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) [Nontrivial (originalBlockFibre b x₀)]

abbrev Top := ActualBlockWreathEmbedding.Top (A:=G) (X:=X)
abbrev Component := ActualBlockWreathEmbedding.Component b hb x₀
abbrev wreath := ActualBlockWreathEmbedding.embedding b hb x₀

variable (P : PrimitiveAffineProfile (Component b hb x₀) (originalBlockFibre b x₀))
    (hprimitive : MulAction.IsPreprimitive (Component b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (origin : originalBlockFibre b x₀)

abbrev Complement := P.complement origin
abbrev localProjection := P.complementProjection origin
abbrev translationKernel : Subgroup G :=
  PermutationalWreathProduct.Compression.kernel (wreath b hb x₀) (localProjection b hb x₀ P origin)

/-- The kernel of the actual component projection is precisely its actual
regular translation subgroup, in the chosen prime-field chart. -/
def localKernelEquiv : (localProjection b hb x₀ P origin).ker ≃* Multiplicative C.V :=
  (MulEquiv.subgroupCongr (P.complementProjection_ker origin)).trans C.equiv

def coordinate (x : X) : translationKernel b hb x₀ P origin →* Multiplicative C.V :=
  (localKernelEquiv b hb x₀ P hprimitive C origin).toMonoidHom.comp
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath b hb x₀) (localProjection b hb x₀ P origin) x)

omit [Finite G] [Finite X] in
theorem coordinates_injective :
    Function.Injective (fun u x => coordinate b hb x₀ P hprimitive C origin x u) := by
  intro u v he
  apply PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
    (wreath b hb x₀) (localProjection b hb x₀ P origin)
    (ActualBlockWreathEmbedding.embedding_injective b hb x₀)
  funext x
  exact (localKernelEquiv b hb x₀ P hprimitive C origin).injective (congrFun he x)

include hprimitive C in
omit [Finite G] [Finite X] in
theorem translationKernel_isMulCommutative :
    IsMulCommutative (translationKernel b hb x₀ P origin) where
  is_comm.comm u v := by
    apply coordinates_injective b hb x₀ P hprimitive C origin
    funext x
    simp only [map_mul]
    exact mul_comm _ _

/-- Conjugation of the actual local translation group, inflated from its
literal quotient by that subgroup. -/
def localChart : ElementaryMinimalNormalChart P.V where
  p := P.p
  p_prime := P.p_prime
  primeFact := C.primeFact
  V := C.V
  equiv := C.equiv

def localRepresentation : Representation (ZMod P.p) (Component b hb x₀) C.V :=
  (localChart b hb x₀ P hprimitive C).quotientRepresentation.ρ.comp
    (QuotientGroup.mk' P.V)

theorem localRepresentation_apply (g : Component b hb x₀) (v : P.V) :
    localRepresentation b hb x₀ P hprimitive C g (C.equiv v).toAdd =
      (C.equiv (MulAut.conjNormal g v)).toAdd :=
  ElementaryMinimalNormalChart.quotientRepresentation_apply
    (localChart b hb x₀ P hprimitive C) g v

def localLinearEquiv (g : Component b hb x₀) : C.V ≃ₗ[ZMod P.p] C.V :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod P.p) C.V
    ((localRepresentation b hb x₀ P hprimitive C).asGroupHom g)

omit [Finite G] [Finite X] [MulAction.IsPretransitive G X] [FaithfulSMul G Ω] in
theorem localLinearEquiv_apply (g : Component b hb x₀) (v : C.V) :
    localLinearEquiv b hb x₀ P hprimitive C g v =
      localRepresentation b hb x₀ P hprimitive C g v := rfl

def blockRepresentation : Representation (ZMod P.p) G (X → C.V) := by
  letI : Fact P.p.Prime := C.primeFact
  exact (PermutationalWreathProduct.functionRepresentation
    (Q:=Top (G:=G) (X:=X)) (I:=X)
      (localRepresentation b hb x₀ P hprimitive C)).comp (wreath b hb x₀)

theorem blockRepresentation_apply (g : G) (v : X → C.V) (x : X) :
    blockRepresentation b hb x₀ P hprimitive C g v x =
      localRepresentation b hb x₀ P hprimitive C
        ((wreath b hb x₀ g).left x) (v (g⁻¹ • x)) := rfl

/-- Each block is transported by an actual invertible linear local map;
no global scalar character or scalar-field extension is introduced. -/
theorem blockRepresentation_single (g : G) (x : X) :
    ∃ L : C.V ≃ₗ[ZMod P.p] C.V, ∀ v : C.V,
      blockRepresentation b hb x₀ P hprimitive C g (Pi.single x v) =
        Pi.single (g • x) (L v) := by
  refine ⟨localLinearEquiv b hb x₀ P hprimitive C
    ((wreath b hb x₀ g).left (g • x)),?_⟩
  intro v
  funext y
  rw [blockRepresentation_apply]
  by_cases hy : y = g • x
  · subst y
    rw [inv_smul_smul,Pi.single_eq_same,Pi.single_eq_same]
    rfl
  · have hn : g⁻¹ • y ≠ x := by
      intro he
      apply hy
      exact (smul_inv_smul g y).symm.trans (congrArg (fun z => g • z) he)
    rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hy,map_zero]

private theorem conjugate_left {D Q I : Type} [Group D] [Group Q] [MulAction Q I]
    (a u : PermutationalWreathProduct D Q I) (hu : u.right = 1) (i : I) :
    (a*u*a⁻¹).left i = a.left i * u.left (a.right⁻¹ • i) * (a.left i)⁻¹ := by
  simp [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left,hu]

private theorem localKernelEquiv_conjugation (g : Component b hb x₀)
    (u : (localProjection b hb x₀ P origin).ker) :
    (localKernelEquiv b hb x₀ P hprimitive C origin (MulAut.conjNormal g u)).toAdd =
      localRepresentation b hb x₀ P hprimitive C g
        (localKernelEquiv b hb x₀ P hprimitive C origin u).toAdd := by
  let v : P.V := MulEquiv.subgroupCongr (P.complementProjection_ker origin) u
  change (C.equiv (MulAut.conjNormal g v)).toAdd =
    localRepresentation b hb x₀ P hprimitive C g (C.equiv v).toAdd
  exact (localRepresentation_apply b hb x₀ P hprimitive C g v).symm

theorem coordinate_conjugation (g : G) (u : translationKernel b hb x₀ P origin) (x : X) :
    (coordinate b hb x₀ P hprimitive C origin x (MulAut.conjNormal g u)).toAdd =
      localRepresentation b hb x₀ P hprimitive C
        ((wreath b hb x₀ g).left x)
        (coordinate b hb x₀ P hprimitive C origin (g⁻¹ • x) u).toAdd := by
  have hu : (wreath b hb x₀ u.val).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff
      (localProjection b hb x₀ P origin) (wreath b hb x₀ u.val)).mp u.property).1
  have hc : PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath b hb x₀) (localProjection b hb x₀ P origin) x (MulAut.conjNormal g u) =
      MulAut.conjNormal ((wreath b hb x₀ g).left x)
        (PermutationalWreathProduct.Compression.kernelCoordinate
          (wreath b hb x₀) (localProjection b hb x₀ P origin) (g⁻¹ • x) u) := by
    apply Subtype.ext
    change (wreath b hb x₀ (g*u.val*g⁻¹)).left x = _
    rw [map_mul,map_mul,map_inv]
    exact conjugate_left _ _ hu x
  change (localKernelEquiv b hb x₀ P hprimitive C origin
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath b hb x₀) (localProjection b hb x₀ P origin) x
        (MulAut.conjNormal g u))).toAdd = _
  rw [hc]
  exact localKernelEquiv_conjugation b hb x₀ P hprimitive C origin _ _

def coordinatesHom : translationKernel b hb x₀ P origin →* Multiplicative (X → C.V) where
  toFun u := Multiplicative.ofAdd (fun x => (coordinate b hb x₀ P hprimitive C origin x u).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_one (coordinate b hb x₀ P hprimitive C origin x))
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd
      (map_mul (coordinate b hb x₀ P hprimitive C origin x) u v)

def kernelSpace : Submodule (ZMod P.p) (X → C.V) :=
  (AddMonoidHom.toMultiplicativeRight.symm
    (coordinatesHom b hb x₀ P hprimitive C origin)).range.toZModSubmodule P.p

def kernelSpaceHom : translationKernel b hb x₀ P origin →* Multiplicative
    (kernelSpace b hb x₀ P hprimitive C origin) where
  toFun u := Multiplicative.ofAdd ⟨(coordinatesHom b hb x₀ P hprimitive C origin u).toAdd,
    ⟨Additive.ofMul u,rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (coordinatesHom b hb x₀ P hprimitive C origin).map_one
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((coordinatesHom b hb x₀ P hprimitive C origin).map_mul u v)

omit [Finite G] [Finite X] in
theorem kernelSpaceHom_bijective : Function.Bijective (kernelSpaceHom b hb x₀ P hprimitive C origin) := by
  constructor
  · intro u v he
    apply coordinates_injective b hb x₀ P hprimitive C origin
    funext x
    apply Multiplicative.toAdd.injective
    exact congrFun (congrArg (fun z : Multiplicative (kernelSpace b hb x₀ P hprimitive C origin) =>
      z.toAdd.val) he) x
  · intro v
    obtain ⟨u,hu⟩ := v.toAdd.property
    refine ⟨u.toMul,?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hu

def kernelChart : translationKernel b hb x₀ P origin ≃* Multiplicative
    (kernelSpace b hb x₀ P hprimitive C origin) :=
  MulEquiv.ofBijective (kernelSpaceHom b hb x₀ P hprimitive C origin)
    (kernelSpaceHom_bijective b hb x₀ P hprimitive C origin)

def elementaryChart : ElementaryMinimalNormalChart (translationKernel b hb x₀ P origin) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Fintype X := Fintype.ofFinite X
  exact {
    p := P.p
    p_prime := P.p_prime
    primeFact := C.primeFact
    V := kernelSpace b hb x₀ P hprimitive C origin
    equiv := kernelChart b hb x₀ P hprimitive C origin }

def kernelInclusion :
    (show Representation (ZMod P.p) G (kernelSpace b hb x₀ P hprimitive C origin) from
      (elementaryChart b hb x₀ P hprimitive C origin).quotientRepresentation.ρ.comp
        (QuotientGroup.mk' (translationKernel b hb x₀ P origin))).IntertwiningMap
          (blockRepresentation b hb x₀ P hprimitive C) where
  toLinearMap := (kernelSpace b hb x₀ P hprimitive C origin).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := (kernelChart b hb x₀ P hprimitive C origin).surjective (Multiplicative.ofAdd v)
    have hv : ((kernelChart b hb x₀ P hprimitive C origin) u).toAdd = v :=
      congrArg Multiplicative.toAdd hu
    rw [←hv]
    change (kernelSpace b hb x₀ P hprimitive C origin).subtype
      ((elementaryChart b hb x₀ P hprimitive C origin).quotientRepresentation.ρ
        (QuotientGroup.mk' (translationKernel b hb x₀ P origin) g)
        (((elementaryChart b hb x₀ P hprimitive C origin).equiv u).toAdd)) = _
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    funext x
    change (coordinate b hb x₀ P hprimitive C origin x (MulAut.conjNormal g u)).toAdd =
      blockRepresentation b hb x₀ P hprimitive C g
        ((coordinatesHom b hb x₀ P hprimitive C origin u).toAdd) x
    rw [blockRepresentation_apply]
    exact coordinate_conjugation b hb x₀ P hprimitive C origin g u x

end SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockCoordinates
