import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.FunctionBlockLocalGeneratorUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupFullProjection
import SymmetricSubgroupAsymptotics.DihedralNormalGenerators
import SymmetricSubgroupAsymptotics.ZModPowerHom
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Row207 has the dihedral group of order18 as actual linear image.
Its rotation has order9; this branch cannot embed in S3 × S3. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207Socles
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def localPerm (g : Equiv.Perm (Fin 4)) : Equiv.Perm Plane :=
  BinaryThreeQuartetLiteralSocles.planeLabel.symm.permCongr g

abbrev R := DihedralGroup 9
abbrev Vector := Fin 3 → Plane
abbrev Lin := W (R := Equiv.Perm (Fin 3)) (I := Fin 3)

def rotation : Lin := ⟨![linearPart (localPerm (Equiv.swap 1 2)),linearPart (localPerm (Equiv.swap 1 2)),linearPart (localPerm (Equiv.swap 1 2 * Equiv.swap 1 3))],(Equiv.swap 0 1 * Equiv.swap 0 2)⟩
def reflection : Lin := ⟨![linearPart (localPerm (Equiv.swap 1 3 * Equiv.swap 1 2)),linearPart (localPerm (Equiv.swap 1 2 * Equiv.swap 1 3)),linearPart (localPerm (Equiv.swap 1 2))],(Equiv.swap 0 1)⟩

def linearImage : R →* Lin where
  toFun q := match q with
    | .r c => rotation^c.val
    | .sr c => reflection * rotation^c.val
  map_one' := rfl
  map_mul' q r := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply LinearEquiv.ext
      intro v
      revert q r i v
      decide +kernel
    · apply Equiv.ext
      intro i
      revert q r i
      decide +kernel

def rho : R →* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun q :=
    { toFun v := fun i => (linearImage q).left i (v ((linearImage q).right⁻¹ i))
      invFun v := fun i => ((linearImage q).left ((linearImage q).right i)).symm
        (v ((linearImage q).right i))
      left_inv := by intro v; funext i; simp
      right_inv := by intro v; funext i; simp
      map_add' := by intro v w; funext i; exact map_add _ _ _
      map_smul' := by intro c v; funext i; exact map_smul ((linearImage q).left i) c (v ((linearImage q).right⁻¹ i)) }
  map_one' := by
    apply LinearEquiv.ext; intro v; funext i
    change (linearImage 1).left i (v ((linearImage 1).right⁻¹ i)) = v i
    rw [map_one]
    rfl
  map_mul' q r := by
    apply LinearEquiv.ext; intro v; funext i
    change (linearImage (q*r)).left i (v ((linearImage (q*r)).right⁻¹ i)) = _
    rw [map_mul]
    rfl

abbrev Affine := LinearSemidirectCoprimeSocleBounds.Model rho

def toWreath : Affine →* BinaryThreeQuartetLiteralSocles.Model (R := Equiv.Perm (Fin 3)) where
  toFun q := ⟨fun i => Multiplicative.ofAdd (q.left.toAdd i),linearImage q.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · exact linearImage.map_one
  map_mul' q r := by
    apply SemidirectProduct.ext
    · rfl
    · exact linearImage.map_mul _ _

def action : Affine →* Equiv.Perm (Fin 12) :=
  BinaryThreeQuartetLiteralSocles.action.comp toWreath

def lifted : Fin 5 → Affine :=
  ![⟨Multiplicative.ofAdd (![![0,0],![0,0],![1,1]] : Vector),DihedralGroup.r 0⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,1]] : Vector),DihedralGroup.r 0⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,1],![1,0]] : Vector),DihedralGroup.r 6⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,0]] : Vector),DihedralGroup.sr 0⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,0]] : Vector),DihedralGroup.sr 1⟩ ]

theorem bindings (i : Fin 5) : action (lifted i) = row207Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

abbrev Odd := Multiplicative (ZMod 9)
def oddMap : Odd →* R := ZModPowerHom.hom 9 (DihedralGroup.r 1) (by decide +kernel)

theorem uniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) 1 := by
  have hcard : Nat.card Odd = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  letI : NeZero (Nat.card Odd : ZMod 2) := ⟨by rw [hcard]; decide⟩
  apply FunctionBlockLocalGeneratorUniform.uniform_of_restriction
    (linearRepresentation rho) (0 : Fin 3) (![1,0] : Plane)
    (Pi.basisFun (ZMod 2) (Fin 2)) oddMap
  · intro j
    refine ⟨Multiplicative.ofAdd (6*j.val : ZMod 9),?_⟩
    rw [Pi.basisFun_apply]
    funext i t
    revert j i t
    decide +kernel
  · intro i
    let n : Fin 3 := ![0,2,1] i
    refine ⟨Multiplicative.ofAdd (n.val : ZMod 9),
      (linearImage (DihedralGroup.r (n.val : ZMod 9))).left i,?_⟩
    intro v
    funext j t
    revert i v j t
    decide +kernel

theorem full_projection : Function.Surjective (projection rho (Subgroup.closure (Set.range lifted))) := by
  let K := Subgroup.closure (Set.range lifted)
  let f := projection rho K
  let x : K := closureGenerators lifted 3 * closureGenerators lifted 4
  let y : K := closureGenerators lifted 3
  have hx : f x = DihedralGroup.r (1 : ZMod 9) := by rfl
  have hy : f y = DihedralGroup.sr (0 : ZMod 9) := by rfl
  intro q
  cases q with
  | r c =>
    refine ⟨x^c.val,?_⟩
    rw [map_pow,hx]
    rw [DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
  | sr c =>
    refine ⟨y*x^c.val,?_⟩
    rw [map_mul,map_pow,hx,hy]
    rw [DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
    simp

theorem quotientSocle (N : Subgroup Row207Top) [N.Normal] :
    SocleNormalGeneratorBound (Row207Top ⧸ N) 3 := by
  let K := Subgroup.closure (Set.range lifted)
  have htuples : ∀ L : Subgroup K, L.Normal →
      ∃ x : Fin 3 → K, Subgroup.normalClosure (Set.range x) = L := by
    intro L hL
    letI := hL
    apply exists_normal_generating_tuple_of_normalGen_le L
    apply LinearSemidirectSubgroupFullProjection.normalGen_le rho K full_projection 1 2 uniform ?_ L
    intro J hJ
    obtain ⟨x,hx⟩ := DihedralNormalGenerators.normal_generating_pairs 9 J hJ
    exact normalGen_le_of_fin_tuple x hx
  let f : K →* Equiv.Perm (Fin 12) := action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) row207Generators
    (Equiv.refl _) (closureGenerators_full lifted) bindings
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) row207Generators
      (Equiv.refl _) (closureGenerators_full lifted) bindings
  exact normal_generating_tuples_of_surjective ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi) htuples
    (finiteGroupSocle _) inferInstance

def family : row207Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row207Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207Socles

end
