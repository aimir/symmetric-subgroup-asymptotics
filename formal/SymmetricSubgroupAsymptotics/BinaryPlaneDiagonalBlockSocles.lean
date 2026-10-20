import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators
import SymmetricSubgroupAsymptotics.FunctionBlockLocalGeneratorUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles
import SymmetricSubgroupAsymptotics.ZModPowerHom

/-! Diagonal local binary-plane maps and arbitrary three-block permutations.
Actual complement subgroups embed in S3 × S3. The two displayed commuting
order-three elements provide a semisimple cyclic restriction on translations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneDiagonalBlockSocles

open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

def localPerm (g : Equiv.Perm (Fin 4)) : Equiv.Perm Plane :=
  BinaryThreeQuartetLiteralSocles.planeLabel.symm.permCongr g

abbrev Blocks := Equiv.Perm (Fin 3)
abbrev Complement := Linear × Blocks
abbrev Vector := Fin 3 → Plane

def rho : Complement →* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun q :=
    { toFun v := fun i => q.1 (v (q.2⁻¹ i))
      invFun v := fun i => q.1.symm (v (q.2 i))
      left_inv := by intro v; funext i; simp
      right_inv := by intro v; funext i; simp
      map_add' := by intro v w; funext i; exact map_add q.1 _ _
      map_smul' := by intro c v; funext i; exact map_smul q.1 _ _ }
  map_one' := by apply LinearEquiv.ext; intro v; rfl
  map_mul' q r := by apply LinearEquiv.ext; intro v; rfl

abbrev Affine := LinearSemidirectCoprimeSocleBounds.Model rho

def diagonalWreath : Complement →* W (R := Blocks) (I := Fin 3) where
  toFun q := ⟨fun _ => q.1,q.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def toWreath : Affine →* BinaryThreeQuartetLiteralSocles.Model (R := Blocks) where
  toFun q := ⟨fun i => Multiplicative.ofAdd (q.left.toAdd i),diagonalWreath q.right⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def flip : Linear := linearPart (localPerm (Equiv.swap 1 3))
def gauge (i : Fin 3) : Linear := if i = 1 then flip else 1

def pointGauge : Plane × Fin 3 ≃ Plane × Fin 3 where
  toFun p := (gauge p.2 p.1,p.2)
  invFun p := ((gauge p.2).symm p.1,p.2)
  left_inv p := by
    apply Prod.ext
    · exact (gauge p.2).symm_apply_apply p.1
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact (gauge p.2).apply_symm_apply p.1
    · rfl

def chart : Plane × Fin 3 ≃ Fin 12 :=
  pointGauge.trans BinaryThreeQuartetLiteralSocles.pointChart

def action : Affine →* Equiv.Perm (Fin 12) :=
  chart.permCongrHom.toMonoidHom.comp
    (BinaryPlanePermutationWreathCoordinates.pointAction.comp toWreath)

abbrev Odd := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
def localSinger : Complement := (singer,1)
def blockRotation : Complement := (1,finRotate 3)

theorem singer_cube : singer^3 = 1 := by
  apply LinearEquiv.ext; intro v; revert v; decide +kernel

def oddMap : Odd →* Complement :=
  MonoidHom.prodMap (ZModPowerHom.hom 3 singer singer_cube)
    (ZModPowerHom.hom 3 (finRotate 3) (by decide +kernel))

theorem uniform_actual (C : Subgroup Complement)
    (hs : localSinger ∈ C) (hr : blockRotation ∈ C) :
    UniformSubrepresentationGeneratorBound
      ((linearRepresentation rho).comp C.subtype) 1 := by
  have hmem (q : Odd) : oddMap q ∈ C := by
    have hs' : localSinger^q.1.toAdd.val ∈ C := C.pow_mem hs _
    have hr' : blockRotation^q.2.toAdd.val ∈ C := C.pow_mem hr _
    have he : oddMap q = localSinger^q.1.toAdd.val * blockRotation^q.2.toAdd.val := by
      apply Prod.ext <;> simp [oddMap,ZModPowerHom.hom,localSinger,blockRotation]
    rw [he]
    exact C.mul_mem hs' hr'
  let f : Odd →* C := oddMap.codRestrict C hmem
  have hcard : Nat.card Odd = 9 := by
    change Nat.card (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) = 9
    rw [Nat.card_prod]
    simp only [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  letI : NeZero (Nat.card Odd : ZMod 2) := ⟨by rw [hcard]; decide⟩
  apply FunctionBlockLocalGeneratorUniform.uniform_of_restriction
    ((linearRepresentation rho).comp C.subtype) (0 : Fin 3) (![1,0] : Plane)
    (Pi.basisFun (ZMod 2) (Fin 2)) f
  · intro j
    refine ⟨(Multiplicative.ofAdd (j.val : ZMod 3),1),?_⟩
    change (linearRepresentation rho) (oddMap (Multiplicative.ofAdd (j.val : ZMod 3),1))
      (Pi.single 0 (![1,0] : Plane)) = Pi.single 0 ((Pi.basisFun (ZMod 2) (Fin 2)) j)
    rw [Pi.basisFun_apply]
    funext i t
    revert j i t
    decide +kernel
  · intro i
    refine ⟨(1,Multiplicative.ofAdd (i.val : ZMod 3)),LinearEquiv.refl (ZMod 2) Plane,?_⟩
    intro v
    change (linearRepresentation rho) (oddMap (1,Multiplicative.ofAdd (i.val : ZMod 3)))
      (Pi.single 0 v) = Pi.single i v
    funext j t
    revert i v j t
    decide +kernel

theorem image_normalGen (C : Subgroup Complement) (N : Subgroup C) [N.Normal] :
    MarkedC4.normalGen N ≤ 2 := by
  apply SymmetricThreeSubgroupNormalGenerators.pair_normalGen_le
    ((BinaryPlaneWreathNormalGenerators.toThree.comp (MonoidHom.fst Linear Blocks)).comp C.subtype)
    ((MonoidHom.snd Linear Blocks).comp C.subtype) ?_ N
  intro x y h
  have h₁ : BinaryPlaneWreathNormalGenerators.toThree x.val.1 =
      BinaryPlaneWreathNormalGenerators.toThree y.val.1 := congrArg Prod.fst h
  have h₂ : x.val.2 = y.val.2 :=
    congrArg (fun z : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) => z.2) h
  exact Subtype.ext (Prod.ext
    (BinaryPlaneWreathNormalGenerators.toThree_injective h₁) h₂)

theorem normalGen_le (K : Subgroup Affine)
    (hs : localSinger ∈ Image rho K) (hr : blockRotation ∈ Image rho K)
    (N : Subgroup K) [N.Normal] : MarkedC4.normalGen N ≤ 3 :=
  LinearSemidirectSubgroupSocles.normalGen_le rho K 1 2
    (uniform_actual (Image rho K) hs hr)
    (fun L hL => by letI := hL; exact image_normalGen (Image rho K) L) N

end SymmetricSubgroupAsymptotics.BinaryPlaneDiagonalBlockSocles

end
