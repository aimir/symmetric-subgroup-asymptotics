import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeLineCoordinates
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators

/-! Actual prime-affine block compression. The actual local component is
embedded in the scalar affine line. Compression by its scalar projection
retains the correlated additive prime-field kernel and its full local
monomial conjugation action. No split or full-product assumption is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeAffineBlockKernelCoordinates
open ScalarAffineLineGroup

variable (p : ℕ) [Fact p.Prime]

variable {G Ω X : Type} [Group G] [MulAction G Ω] [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X)

abbrev Top := ActualBlockWreathEmbedding.Top (A:=G) (X:=X)
abbrev Component := ActualBlockWreathEmbedding.Component b hb x₀

/-- Coordinates of the actual component, supplied below from its actual
prime-degree affine profile. Injectivity is part of this honest group chart. -/
structure ComponentCoordinates where
  hom : Component b hb x₀ →* Line (ZMod p)
  injective : Function.Injective hom

variable (C : ComponentCoordinates p b hb x₀)

/-- The actual original wreath embedding, with only its base coordinates
changed through the faithful component chart. -/
def wreath : G →* PermutationalWreathProduct (Line (ZMod p)) (Top (G:=G) (X:=X)) X :=
  (PermutationalWreathProduct.mapBase C.hom).comp
    (ActualBlockWreathEmbedding.embedding b hb x₀)

theorem wreath_injective : Function.Injective (wreath p b hb x₀ C) := by
  intro g h he
  apply ActualBlockWreathEmbedding.embedding_injective b hb x₀
  apply PermutationalWreathProduct.ext
  · funext x
    apply C.injective
    exact congrArg (fun w => w.left x) he
  · have hr : (wreath p b hb x₀ C g).right = (wreath p b hb x₀ C h).right :=
      congrArg (fun w : PermutationalWreathProduct (Line (ZMod p))
        (Top (G:=G) (X:=X)) X => w.right) he
    exact hr

/-- The original additive block kernel is defined as an actual hom kernel,
so ambient normality is retained before any chart is chosen. -/
abbrev translationKernel : Subgroup G :=
  PermutationalWreathProduct.Compression.kernel (wreath p b hb x₀ C) (scalar (ZMod p))

def coordinate (x : X) : translationKernel p b hb x₀ C →* Multiplicative (ZMod p) :=
  (translationKernelEquiv (ZMod p)).toMonoidHom.comp
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath p b hb x₀ C) (scalar (ZMod p)) x)

theorem coordinates_injective :
    Function.Injective (fun u x => coordinate p b hb x₀ C x u) := by
  intro u v he
  apply PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
    (wreath p b hb x₀ C) (scalar (ZMod p)) (wreath_injective p b hb x₀ C)
  funext x
  exact (translationKernelEquiv (ZMod p)).injective (congrFun he x)

theorem translationKernel_isMulCommutative : IsMulCommutative (translationKernel p b hb x₀ C) where
  is_comm.comm u v := by
    apply coordinates_injective p b hb x₀ C
    funext x
    simp only [map_mul]
    exact mul_comm _ _

private def scalarRepresentation : Representation (ZMod p) (Line (ZMod p)) (ZMod p) where
  toFun s := (s.right : ZMod p) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    change (↑((scalar (ZMod p)) 1) : ZMod p) * z = z
    rw [map_one,Units.val_one,one_mul]
  map_mul' s t := by
    apply LinearMap.ext
    intro z
    change (↑((scalar (ZMod p)) (s*t)) : ZMod p) * z =
      (↑((scalar (ZMod p)) s) : ZMod p) * ((↑((scalar (ZMod p)) t) : ZMod p) * z)
    rw [map_mul,Units.val_mul,mul_assoc]

/-- Destination-indexed original local scalars, including all block twists. -/
def monomialRepresentation : Representation (ZMod p) G (X → ZMod p) :=
  (PermutationalWreathProduct.functionRepresentation
    (Q:=Top (G:=G) (X:=X)) (I:=X) (scalarRepresentation p)).comp (wreath p b hb x₀ C)

theorem monomialRepresentation_apply (g : G) (v : X → ZMod p) (x : X) :
    monomialRepresentation p b hb x₀ C g v x =
      (↑((wreath p b hb x₀ C g).left x).right : ZMod p) * v (g⁻¹ • x) := rfl

/-- A transported coordinate delta has an actual nonzero local unit,
with no assumption that this unit is independent of the coordinate. -/
theorem monomialRepresentation_single (g : G) (x : X) :
    ∃ u : (ZMod p)ˣ, monomialRepresentation p b hb x₀ C g (Pi.single x 1) =
      (u : ZMod p) • (Pi.single (g • x) 1 : X → ZMod p) := by
  let u := ((wreath p b hb x₀ C g).left (g • x)).right
  refine ⟨u,?_⟩
  funext y
  rw [monomialRepresentation_apply]
  by_cases hy : y = g • x
  · subst y
    simp only [Pi.single_eq_same,mul_one,Pi.smul_apply,smul_eq_mul]
    change (↑((wreath p b hb x₀ C g).left (g • x)).right : ZMod p) *
      (Pi.single x (1 : ZMod p) : X → ZMod p) ((g⁻¹ : G) • (g • x)) = (u : ZMod p)
    rw [inv_smul_smul,Pi.single_eq_same,mul_one]
  · have hn : g⁻¹ • y ≠ x := by
      intro he
      apply hy
      exact (smul_inv_smul g y).symm.trans (congrArg (fun z => g • z) he)
    simp only [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hy,mul_zero,Pi.smul_apply,
      smul_zero]

private theorem conjugate_left {D Q I : Type} [Group D] [Group Q] [MulAction Q I]
    (a u : PermutationalWreathProduct D Q I) (hu : u.right = 1) (i : I) :
    (a*u*a⁻¹).left i = a.left i * u.left (a.right⁻¹ • i) * (a.left i)⁻¹ := by
  simp [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left,hu]

/-- Original ambient conjugation transports each translation coordinate
with the scalar of its actual local affine transporter. -/
theorem coordinate_conjugation (g : G) (u : translationKernel p b hb x₀ C) (x : X) :
    (coordinate p b hb x₀ C x (MulAut.conjNormal g u)).toAdd =
      (↑((wreath p b hb x₀ C g).left x).right : ZMod p) *
        (coordinate p b hb x₀ C (g⁻¹ • x) u).toAdd := by
  have hu : (wreath p b hb x₀ C u.val).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff (scalar (ZMod p))
      (wreath p b hb x₀ C u.val)).mp u.property).1
  have hc : PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath p b hb x₀ C) (scalar (ZMod p)) x (MulAut.conjNormal g u) =
      MulAut.conjNormal ((wreath p b hb x₀ C g).left x)
        (PermutationalWreathProduct.Compression.kernelCoordinate
          (wreath p b hb x₀ C) (scalar (ZMod p)) (g⁻¹ • x) u) := by
    apply Subtype.ext
    change (wreath p b hb x₀ C (g*u.val*g⁻¹)).left x = _
    rw [map_mul,map_mul,map_inv]
    exact conjugate_left _ _ hu x
  change ((translationKernelEquiv (ZMod p)) (PermutationalWreathProduct.Compression.kernelCoordinate
    (wreath p b hb x₀ C) (scalar (ZMod p)) x (MulAut.conjNormal g u))).toAdd = _
  rw [hc]
  exact translationKernelEquiv_conjugation (ZMod p) _ _

def coordinatesHom : translationKernel p b hb x₀ C →* Multiplicative (X → ZMod p) where
  toFun u := Multiplicative.ofAdd (fun x => (coordinate p b hb x₀ C x u).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_one (coordinate p b hb x₀ C x))
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_mul (coordinate p b hb x₀ C x) u v)

theorem coordinatesHom_injective : Function.Injective (coordinatesHom p b hb x₀ C) := by
  intro u v he
  apply coordinates_injective p b hb x₀ C
  funext x
  apply Multiplicative.toAdd.injective
  exact congrFun (congrArg Multiplicative.toAdd he) x

def kernelSpace : Submodule (ZMod p) (X → ZMod p) :=
  (AddMonoidHom.toMultiplicativeRight.symm (coordinatesHom p b hb x₀ C)).range.toZModSubmodule p

def kernelSpaceHom : translationKernel p b hb x₀ C →* Multiplicative (kernelSpace p b hb x₀ C) where
  toFun u := Multiplicative.ofAdd ⟨(coordinatesHom p b hb x₀ C u).toAdd,
    ⟨Additive.ofMul u,rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (coordinatesHom p b hb x₀ C).map_one
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((coordinatesHom p b hb x₀ C).map_mul u v)

theorem kernelSpaceHom_bijective : Function.Bijective (kernelSpaceHom p b hb x₀ C) := by
  constructor
  · intro u v he
    apply coordinatesHom_injective p b hb x₀ C
    exact congrArg (fun z : Multiplicative (kernelSpace p b hb x₀ C) =>
      Multiplicative.ofAdd z.toAdd.val) he
  · intro v
    obtain ⟨u,hu⟩ := v.toAdd.property
    refine ⟨u.toMul,?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hu

def kernelChart : translationKernel p b hb x₀ C ≃* Multiplicative (kernelSpace p b hb x₀ C) :=
  MulEquiv.ofBijective (kernelSpaceHom p b hb x₀ C) (kernelSpaceHom_bijective p b hb x₀ C)

variable [Finite X]

def elementaryChart : ElementaryMinimalNormalChart (translationKernel p b hb x₀ C) := by
  letI : Fintype X := Fintype.ofFinite X
  exact {
    p := p
    p_prime := Fact.out
    V := kernelSpace p b hb x₀ C
    equiv := kernelChart p b hb x₀ C }

/-- The same original conjugation representation embeds into its actual
monomial coordinate space. This is not an image-faithfulness premise. -/
def kernelInclusion :
    (show Representation (ZMod p) G (kernelSpace p b hb x₀ C) from
      (elementaryChart p b hb x₀ C).quotientRepresentation.ρ.comp
        (QuotientGroup.mk' (translationKernel p b hb x₀ C))).IntertwiningMap
          (monomialRepresentation p b hb x₀ C) where
  toLinearMap := (kernelSpace p b hb x₀ C).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := (kernelChart p b hb x₀ C).surjective (Multiplicative.ofAdd v)
    have hv : ((kernelChart p b hb x₀ C) u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv]
    change (kernelSpace p b hb x₀ C).subtype
      ((elementaryChart p b hb x₀ C).quotientRepresentation.ρ
        (QuotientGroup.mk' (translationKernel p b hb x₀ C) g)
        (((elementaryChart p b hb x₀ C).equiv u).toAdd)) = _
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    funext x
    change (coordinate p b hb x₀ C x (MulAut.conjNormal g u)).toAdd =
      monomialRepresentation p b hb x₀ C g ((coordinatesHom p b hb x₀ C u).toAdd) x
    rw [monomialRepresentation_apply]
    exact coordinate_conjugation p b hb x₀ C g u x

/-- A literal affine profile on the actual prime-sized block supplies the
component chart. This installer derives it from the regular translation
subgroup and does not ask for a separate affine-embedding premise. -/
def componentCoordinatesOfProfile [Finite Ω]
    (P : PrimitiveAffineProfile (Component b hb x₀) (originalBlockFibre b x₀))
    (ω₀ : originalBlockFibre b x₀)
    (hdegree : Nat.card (originalBlockFibre b x₀) = p) :
    ComponentCoordinates p b hb x₀ where
  hom := PrimitiveAffinePrimeLineCoordinates.coordinates p P ω₀ hdegree
  injective := PrimitiveAffinePrimeLineCoordinates.coordinates_injective p P ω₀ hdegree

end SymmetricSubgroupAsymptotics.PrimeAffineBlockKernelCoordinates
