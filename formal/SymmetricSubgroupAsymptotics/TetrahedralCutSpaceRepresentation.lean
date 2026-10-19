import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceCoinvariantHead
import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads
import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceRepresentation
open TetrahedralCutSpaceCoinvariantHead (Bit Vector A B D0 D1)
open AlternatingEdgeOriginalProjectorHeads (Top a t)

def coefficient (v : Vector) (i : Fin 4) : Bit := ![0,v 0,v 1,v 2] i
def acted (p : Equiv.Perm (Fin 4)) (v : Vector) (i : Fin 3) : Bit :=
  coefficient v (p⁻¹ (![1,2,3] i))+coefficient v (p⁻¹ 0)

def rho : Representation Bit (Equiv.Perm (Fin 4)) Vector where
  toFun p :=
    { toFun := acted p
      map_add' := by
        intro v w
        funext i
        revert p v w i
        decide +kernel
      map_smul' := by
        intro r v
        funext i
        revert p r v i
        decide +kernel }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    revert v i
    decide +kernel
  map_mul' p q := by
    apply LinearMap.ext
    intro v
    funext i
    revert p q v i
    decide +kernel

def beta : Representation Bit Top Vector := rho.comp (alternatingGroup (Fin 4)).subtype

theorem beta_a : ∀ v,beta a v=A v := by decide +kernel
theorem beta_t1 : ∀ v,beta (t 1) v=B v := by decide +kernel
theorem beta_t2 : ∀ v,(1+beta (t 2)) v=D1 v := by decide +kernel

def cubicWitness : LiteralPolynomialSpanWitness A 1 2 where
  vectors _ m := Pi.single m 1
  step := by decide +kernel
  selected i := (0,i)
  coefficient i j := if i=j then 1 else 0
  point_eq := by decide +kernel

theorem uniform_one : UniformSubrepresentationGeneratorBound beta 1 := by
  apply cubicWitness.uniform beta (MonoidAlgebra.single a 1)
  rw [Representation.asAlgebraHom_single_one]
  apply LinearMap.ext
  intro v
  exact (beta_a v).symm
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceRepresentation
