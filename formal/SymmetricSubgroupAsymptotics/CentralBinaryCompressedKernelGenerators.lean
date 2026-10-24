import SymmetricSubgroupAsymptotics.PermutationalWreathElementaryCompression
import SymmetricSubgroupAsymptotics.TransitivePermutationModuleGenerators
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! A central binary local kernel costs at most half the number of
transitively permuted blocks. The wreath compression and all correlations
are literal; its elementary chart is the existing actual image chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CentralBinaryCompressedKernelGenerators
open PermutationalWreathProduct

variable {A D S Q I : Type} [Group A] [Finite A] [Group D] [Finite D]
    [Group S] [Group Q] [Fintype I] [Nonempty I] [MulAction Q I] [MulAction A I]
    (rho : A →* PermutationalWreathProduct D Q I) (phi : D →* S)
    (e : Multiplicative (ZMod 2) ≃* phi.ker)
    (hrho : Function.Injective rho)
    (hcentral : ∀ (d : D) (u : phi.ker), MulAut.conjNormal d u = u)
    (hact : ∀ (a : A) (i : I), (rho a).right • i = a • i)

omit [Finite D] [Fintype I] [Nonempty I] in
private theorem conjugate_left (a u : PermutationalWreathProduct D Q I)
    (hu : u.right = 1) (i : I) :
    (a*u*a⁻¹).left i = a.left i * u.left (a.right⁻¹ • i) * (a.left i)⁻¹ := by
  simp [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left,hu]

include hcentral hact in
theorem coordinate_conjugation (g : A) (u : Compression.kernel rho phi) (i : I) :
    (Compression.elementaryCoordinate rho phi e i (MulAut.conjNormal g u)).toAdd =
      (Compression.elementaryCoordinate rho phi e (g⁻¹ • i) u).toAdd := by
  have hu : (rho u.val).right = 1 :=
    ((mem_mapBase_ker_iff phi (rho u.val)).mp u.property).1
  have hr : (rho g).right⁻¹ • i = g⁻¹ • i := by
    simpa only [map_inv,inv_right] using hact g⁻¹ i
  have hc : Compression.kernelCoordinate rho phi i (MulAut.conjNormal g u) =
      MulAut.conjNormal ((rho g).left i)
        (Compression.kernelCoordinate rho phi (g⁻¹ • i) u) := by
    apply Subtype.ext
    change (rho (g*u.val*g⁻¹)).left i = _
    rw [map_mul,map_mul,map_inv]
    rw [conjugate_left _ _ hu i,hr]
    rfl
  change (e.symm (Compression.kernelCoordinate rho phi i
    (MulAut.conjNormal g u))).toAdd = _
  rw [hc,hcentral]
  rfl

include hcentral hact in
def kernelInclusion :
    (show Representation (ZMod 2) A (Compression.ElementarySubmodule (p:=2) rho phi e) from
      (Compression.kernelElementaryChart (p:=2) rho phi e hrho).quotientRepresentation.ρ.comp
        (QuotientGroup.mk' (Compression.kernel rho phi))).IntertwiningMap
      (permutationFunctionRepresentation (ZMod 2) A I) where
  toLinearMap := (Compression.ElementarySubmodule (p:=2) rho phi e).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let C := Compression.kernelElementaryChart (p:=2) rho phi e hrho
    obtain ⟨u,hu⟩ := C.equiv.surjective (Multiplicative.ofAdd v)
    have hv : (C.equiv u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv]
    change (Compression.ElementarySubmodule (p:=2) rho phi e).subtype
      (C.quotientRepresentation.ρ (QuotientGroup.mk' (Compression.kernel rho phi) g)
        (C.equiv u).toAdd) = _
    rw [ElementaryMinimalNormalChart.quotientRepresentation_apply]
    funext i
    change (Compression.elementaryCoordinate rho phi e i
      (MulAut.conjNormal g u)).toAdd =
        (Compression.elementaryCoordinate rho phi e (g⁻¹ • i) u).toAdd
    exact coordinate_conjugation rho phi e hcentral hact g u i

include e hrho hcentral hact in
theorem normalGen_le_half [Nontrivial I] [MulAction.IsPretransitive A I] :
    MarkedC4.normalGen (Compression.kernel rho phi) ≤ Nat.card I / 2 := by
  let C := Compression.kernelElementaryChart (p:=2) rho phi e hrho
  have huniform := TransitivePermutationModuleGenerators.uniform_of_transitive (ZMod 2)
    (G:=A) (X:=I)
  have hquot : UniformSubrepresentationGeneratorBound C.quotientRepresentation.ρ
      (Nat.card I / 2) := by
    apply UniformSubrepresentationGeneratorBound.of_comp C.quotientRepresentation.ρ
      (QuotientGroup.mk' (Compression.kernel rho phi))
    change UniformSubrepresentationGeneratorBound
      (show Representation (ZMod 2) A (Compression.ElementarySubmodule (p:=2) rho phi e) from
        C.quotientRepresentation.ρ.comp (QuotientGroup.mk' (Compression.kernel rho phi)))
          (Nat.card I / 2)
    exact huniform.of_injective (kernelInclusion rho phi e hrho hcentral hact)
      (Compression.ElementarySubmodule (p:=2) rho phi e).subtype_injective
  exact ElementaryUniformNormalGenerators.kernel_normalGen_le
    (Compression.kernel rho phi) C (Nat.card I / 2) hquot
      (Compression.kernel rho phi) le_rfl

end SymmetricSubgroupAsymptotics.CentralBinaryCompressedKernelGenerators
