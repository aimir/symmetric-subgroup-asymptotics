import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators

/-! Actual correlated rotation coordinates for three-point blocks.
The original wreath embedding is relabelled on its actual base fibre.
Compression by the literal S3 sign defines an ambient normal kernel.
Its faithful ternary coordinates intertwine original conjugation with
an arbitrary coordinate-dependent monomial action. No global scalar
character, split extension or full product is substituted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryBlockKernelCoordinates
open OddMarkerTernaryChart

variable {G Ω X : Type} [Group G] [MulAction G Ω] [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (e : Fin 3 ≃ originalBlockFibre b x₀)

abbrev Top := ActualBlockWreathEmbedding.Top (A:=G) (X:=X)
abbrev Component := ActualBlockWreathEmbedding.Component b hb x₀

def componentPermutation : Component b hb x₀ →* OddMarkerGroup :=
  e.symm.permCongrHom.toMonoidHom.comp (Component b hb x₀).subtype

omit [MulAction.IsPretransitive G X] [FaithfulSMul G Ω] in
theorem componentPermutation_injective : Function.Injective (componentPermutation b hb x₀ e) :=
  e.symm.permCongrHom.injective.comp Subtype.coe_injective

/-- A faithful embedding of the original group, not an independent full
wreath product action. Only the actual base-fibre labels change. -/
def wreath : G →* PermutationalWreathProduct OddMarkerGroup (Top (G:=G) (X:=X)) X :=
  (PermutationalWreathProduct.mapBase (componentPermutation b hb x₀ e)).comp
    (ActualBlockWreathEmbedding.embedding b hb x₀)

theorem wreath_injective : Function.Injective (wreath b hb x₀ e) := by
  intro g h he
  apply ActualBlockWreathEmbedding.embedding_injective b hb x₀
  apply PermutationalWreathProduct.ext
  · funext x
    apply componentPermutation_injective b hb x₀ e
    exact congrArg (fun w => w.left x) he
  · have hr : (wreath b hb x₀ e g).right = (wreath b hb x₀ e h).right :=
      congrArg (fun w : PermutationalWreathProduct OddMarkerGroup (Top (G:=G) (X:=X)) X =>
        w.right) he
    exact hr

/-- The original all-even block kernel is defined as an actual hom kernel,
so ambient normality is retained before any chart is chosen. -/
abbrev evenKernel : Subgroup G :=
  PermutationalWreathProduct.Compression.kernel (wreath b hb x₀ e) oddMarkerSign

def coordinate (x : X) : evenKernel b hb x₀ e →* Multiplicative (ZMod 3) :=
  chart.symm.toMonoidHom.comp
    (PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath b hb x₀ e) oddMarkerSign x)

theorem coordinates_injective :
    Function.Injective (fun u x => coordinate b hb x₀ e x u) := by
  intro u v he
  apply PermutationalWreathProduct.Compression.kernelCoordinate_joint_injective
    (wreath b hb x₀ e) oddMarkerSign (wreath_injective b hb x₀ e)
  funext x
  exact chart.symm.injective (congrFun he x)

theorem evenKernel_isMulCommutative : IsMulCommutative (evenKernel b hb x₀ e) where
  is_comm.comm u v := by
    apply coordinates_injective b hb x₀ e
    funext x
    simp only [map_mul]
    exact mul_comm _ _

private def signRepresentation : Representation (ZMod 3) OddMarkerGroup (ZMod 3) where
  toFun s := signScalar (oddMarkerSign s) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    change signScalar (oddMarkerSign 1) * z = z
    rw [map_one,signScalar_one,one_mul]
  map_mul' s t := by
    apply LinearMap.ext
    intro z
    change signScalar (oddMarkerSign (s*t)) * z =
      signScalar (oddMarkerSign s) * (signScalar (oddMarkerSign t) * z)
    rw [map_mul,signScalar_mul,mul_assoc]

/-- Destination-indexed original local signs, including all block twists. -/
def monomialRepresentation : Representation (ZMod 3) G (X → ZMod 3) :=
  (PermutationalWreathProduct.functionRepresentation
    (Q:=Top (G:=G) (X:=X)) (I:=X) signRepresentation).comp (wreath b hb x₀ e)

theorem monomialRepresentation_apply (g : G) (v : X → ZMod 3) (x : X) :
    monomialRepresentation b hb x₀ e g v x =
      signScalar (oddMarkerSign ((wreath b hb x₀ e g).left x)) * v (g⁻¹ • x) := rfl

/-- A transported coordinate delta has an actual nonzero local unit,
with no assumption that this unit is independent of the coordinate. -/
theorem monomialRepresentation_single (g : G) (x : X) :
    ∃ u : (ZMod 3)ˣ, monomialRepresentation b hb x₀ e g (Pi.single x 1) =
      (u : ZMod 3) • (Pi.single (g • x) 1 : X → ZMod 3) := by
  let u := signUnitHom (oddMarkerSign ((wreath b hb x₀ e g).left (g • x)))
  refine ⟨u,?_⟩
  funext y
  rw [monomialRepresentation_apply]
  by_cases hy : y = g • x
  · subst y
    simp only [Pi.single_eq_same,mul_one,Pi.smul_apply,smul_eq_mul]
    change signScalar (oddMarkerSign ((wreath b hb x₀ e g).left (g • x))) *
      (Pi.single x (1 : ZMod 3) : X → ZMod 3) ((g⁻¹ : G) • (g • x)) = (u : ZMod 3)
    rw [inv_smul_smul,Pi.single_eq_same,mul_one]
    rfl
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

/-- Original ambient conjugation transports each rotation coordinate
with the sign of its actual local S3 transporter. -/
theorem coordinate_conjugation (g : G) (u : evenKernel b hb x₀ e) (x : X) :
    (coordinate b hb x₀ e x (MulAut.conjNormal g u)).toAdd =
      signScalar (oddMarkerSign ((wreath b hb x₀ e g).left x)) *
        (coordinate b hb x₀ e (g⁻¹ • x) u).toAdd := by
  have hu : (wreath b hb x₀ e u.val).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff oddMarkerSign
      (wreath b hb x₀ e u.val)).mp u.property).1
  have hc : PermutationalWreathProduct.Compression.kernelCoordinate
      (wreath b hb x₀ e) oddMarkerSign x (MulAut.conjNormal g u) =
      MulAut.conjNormal ((wreath b hb x₀ e g).left x)
        (PermutationalWreathProduct.Compression.kernelCoordinate
          (wreath b hb x₀ e) oddMarkerSign (g⁻¹ • x) u) := by
    apply Subtype.ext
    change (wreath b hb x₀ e (g*u.val*g⁻¹)).left x = _
    rw [map_mul,map_mul,map_inv]
    exact conjugate_left _ _ hu x
  change (chart.symm (PermutationalWreathProduct.Compression.kernelCoordinate
    (wreath b hb x₀ e) oddMarkerSign x (MulAut.conjNormal g u))).toAdd = _
  rw [hc]
  exact chart_symm_conjugate _ _

def coordinatesHom : evenKernel b hb x₀ e →* Multiplicative (X → ZMod 3) where
  toFun u := Multiplicative.ofAdd (fun x => (coordinate b hb x₀ e x u).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_one (coordinate b hb x₀ e x))
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext x
    exact congrArg Multiplicative.toAdd (map_mul (coordinate b hb x₀ e x) u v)

theorem coordinatesHom_injective : Function.Injective (coordinatesHom b hb x₀ e) := by
  intro u v he
  apply coordinates_injective b hb x₀ e
  funext x
  apply Multiplicative.toAdd.injective
  exact congrFun (congrArg Multiplicative.toAdd he) x

def kernelSpace : Submodule (ZMod 3) (X → ZMod 3) :=
  (AddMonoidHom.toMultiplicativeRight.symm (coordinatesHom b hb x₀ e)).range.toZModSubmodule 3

def kernelSpaceHom : evenKernel b hb x₀ e →* Multiplicative (kernelSpace b hb x₀ e) where
  toFun u := Multiplicative.ofAdd ⟨(coordinatesHom b hb x₀ e u).toAdd,
    ⟨Additive.ofMul u,rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (coordinatesHom b hb x₀ e).map_one
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((coordinatesHom b hb x₀ e).map_mul u v)

theorem kernelSpaceHom_bijective : Function.Bijective (kernelSpaceHom b hb x₀ e) := by
  constructor
  · intro u v he
    apply coordinatesHom_injective b hb x₀ e
    exact congrArg (fun z : Multiplicative (kernelSpace b hb x₀ e) =>
      Multiplicative.ofAdd z.toAdd.val) he
  · intro v
    obtain ⟨u,hu⟩ := v.toAdd.property
    refine ⟨u.toMul,?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hu

def kernelChart : evenKernel b hb x₀ e ≃* Multiplicative (kernelSpace b hb x₀ e) :=
  MulEquiv.ofBijective (kernelSpaceHom b hb x₀ e) (kernelSpaceHom_bijective b hb x₀ e)

variable [Finite X]

def elementaryChart : ElementaryMinimalNormalChart (evenKernel b hb x₀ e) := by
  letI : Fintype X := Fintype.ofFinite X
  exact {
    p := 3
    p_prime := Nat.prime_three
    V := kernelSpace b hb x₀ e
    equiv := kernelChart b hb x₀ e }

/-- The same original conjugation representation embeds into its actual
monomial coordinate space. This is not an image-faithfulness premise. -/
def kernelInclusion :
    (show Representation (ZMod 3) G (kernelSpace b hb x₀ e) from
      (elementaryChart b hb x₀ e).quotientRepresentation.ρ.comp
        (QuotientGroup.mk' (evenKernel b hb x₀ e))).IntertwiningMap
          (monomialRepresentation b hb x₀ e) where
  toLinearMap := (kernelSpace b hb x₀ e).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := (kernelChart b hb x₀ e).surjective (Multiplicative.ofAdd v)
    have hv : ((kernelChart b hb x₀ e) u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv]
    change (kernelSpace b hb x₀ e).subtype
      ((elementaryChart b hb x₀ e).quotientRepresentation.ρ
        (QuotientGroup.mk' (evenKernel b hb x₀ e) g)
        (((elementaryChart b hb x₀ e).equiv u).toAdd)) = _
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    funext x
    change (coordinate b hb x₀ e x (MulAut.conjNormal g u)).toAdd =
      monomialRepresentation b hb x₀ e g ((coordinatesHom b hb x₀ e u).toAdd) x
    rw [monomialRepresentation_apply]
    exact coordinate_conjugation b hb x₀ e g u x

end SymmetricSubgroupAsymptotics.TernaryBlockKernelCoordinates
