import SymmetricSubgroupAsymptotics.CFSGCartanPowerIndex
import Mathlib.Algebra.Group.Equiv.Basic

/-! A diagram-equivariant monomial endomorphism restricts to the literal
field-diagram fixed tuples. Its restricted kernel injects into the full
kernel, so a checked one-factor Smith certificate bounds its image index.
No surjectivity on fixed points is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDiagramMonomialSubgroup
open CFSGIntegerMatrixPowerHom CFSGCartanPowerIndex

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : Type*} [CommGroup G]

/-- Tuples whose diagram permutation agrees with the given group automorphism. -/
def diagramTuples (p : Equiv.Perm I) (sigma : MulAut G) : Subgroup (I → G) where
  carrier := {x | ∀ i,sigma (x i)=x (p i)}
  one_mem' := by intro i; exact map_one sigma
  mul_mem' := by
    intro x y hx hy i
    change sigma (x i*y i)=x (p i)*y (p i)
    rw [map_mul,hx i,hy i]
  inv_mem' := by
    intro x hx i
    change sigma ((x i)⁻¹)=(x (p i))⁻¹
    rw [map_inv,hx i]

variable (p : Equiv.Perm I) (sigma : MulAut G) (A : Matrix I I ℤ)
variable (hA : ∀ i j,A (p i) (p j)=A i j)
include hA

omit [DecidableEq I] in
theorem powerHom_mem (x : I → G) (hx : x∈diagramTuples p sigma) :
    powerHom A x∈diagramTuples p sigma := by
  change ∀ i,sigma (x i)=x (p i) at hx
  intro i
  change sigma (∏ j,x j ^ A i j)=∏ j,x j ^ A (p i) j
  rw [map_prod]
  simp only [map_zpow]
  simp_rw [hx]
  exact Fintype.prod_equiv p _ _ (fun j => by rw [hA])

/-- The actual endomorphism of diagram-fixed tuples. -/
def fixedPowerHom : diagramTuples p sigma →* diagramTuples p sigma where
  toFun x := ⟨powerHom A x.val,powerHom_mem p sigma A hA x.val x.property⟩
  map_one' := Subtype.ext (map_one (powerHom A))
  map_mul' x y := Subtype.ext (map_mul (powerHom A) x.val y.val)

@[simp] theorem fixedPowerHom_val (x : diagramTuples p sigma) :
    (fixedPowerHom p sigma A hA x).val=powerHom A x.val := rfl

def kernelInclusion (x : (fixedPowerHom p sigma A hA).ker) :
    (powerHom A : (I → G) →* (I → G)).ker :=
  ⟨x.val.val,congrArg Subtype.val x.property⟩

theorem kernelInclusion_injective :
    Function.Injective (kernelInclusion p sigma A hA) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (powerHom A : (I → G) →* (I → G)).ker => z.val) he

variable (K : Type*) [Field K] [Finite K]
variable (sigmaK : MulAut Kˣ) {i : I} {d : ℕ}

/-- The restricted fixed-tuple image obeys the SAME Smith-factor bound. -/
theorem fixedPowerHom_range_index_le (S : OneFactorCertificate A i d) [NeZero d] :
    (fixedPowerHom p sigmaK A hA).range.index≤d := by
  rw [Subgroup.index_range]
  calc
    Nat.card (fixedPowerHom p sigmaK A hA).ker≤Nat.card (rootsOfUnity d K) :=
      Nat.card_le_card_of_injective
        (fun x => kernelRoot S K (kernelInclusion p sigmaK A hA x))
        ((kernelRoot_injective S K).comp (kernelInclusion_injective p sigmaK A hA))
    _=Fintype.card (rootsOfUnity d K) := Nat.card_eq_fintype_card
    _≤d := card_rootsOfUnity (R := K) (k := d)

end SymmetricSubgroupAsymptotics.CFSGDiagramMonomialSubgroup
