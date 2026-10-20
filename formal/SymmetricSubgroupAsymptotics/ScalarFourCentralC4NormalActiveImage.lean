import SymmetricSubgroupAsymptotics.ScalarFourQuadraticField
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
import SymmetricSubgroupAsymptotics.BinaryCubicStableScalarSubspace

/-! The active image of an actual original normal denominator is an F4
subspace with precisely its original carrier. No complement is chosen. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open BinaryQuadraticField
variable {Q T : Type} [Group Q] [Group T] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

def fieldActive : D.top.ker →* Multiplicative (Fin d → Scalar) :=
  (ScalarFourQuadraticField.tupleEquivalence d).toMonoidHom.comp D.active

def binaryActiveImage (L : Subgroup D.top.ker) : Submodule (ZMod 2) (Fin d → Scalar) where
  carrier := {v | ∃ k ∈ L, (D.fieldActive k).toAdd=v}
  zero_mem' := ⟨1,L.one_mem,by rw [map_one]; rfl⟩
  add_mem' := by
    rintro v w ⟨k,hk,rfl⟩ ⟨l,hl,rfl⟩
    refine ⟨k*l,L.mul_mem hk hl,?_⟩
    rw [map_mul]
    rfl
  smul_mem' := by
    intro a v hv
    fin_cases a
    · change (0 : ZMod 2) • v ∈ {v | ∃ k ∈ L, (D.fieldActive k).toAdd=v}
      simpa only [zero_smul] using
        (show ∃ k ∈ L, (D.fieldActive k).toAdd=0 from
          ⟨1,L.one_mem,by rw [map_one]; rfl⟩)
    · change (1 : ZMod 2) • v ∈ {v | ∃ k ∈ L, (D.fieldActive k).toAdd=v}
      simpa only [one_smul] using hv

theorem binaryActiveImage_omega (L : Subgroup D.top.ker)
    (n : Q) (hn : D.top n=D.cubic)
    (hL : ∀ k∈L, MulAut.conjNormal n k∈L) :
    ∀ v∈D.binaryActiveImage L, (fun j => omega*v j)∈D.binaryActiveImage L := by
  rintro v ⟨k,hk,rfl⟩
  refine ⟨MulAut.conjNormal n k,hL k hk,?_⟩
  change (ScalarFourQuadraticField.tupleEquivalence d
      (D.active (MulAut.conjNormal n k))).toAdd=
    fun j => omega*(ScalarFourQuadraticField.tupleEquivalence d (D.active k)).toAdd j
  have he : D.active (MulAut.conjNormal n k)=
      fun j => scalarFourTwist 1 (D.active k j) := by
    funext j
    exact D.cubic_action n hn k j
  rw [he]
  exact ScalarFourQuadraticField.tuple_twist d (D.active k)

def scalarActiveImage (L : Subgroup D.top.ker)
    (n : Q) (hn : D.top n=D.cubic)
    (hL : ∀ k∈L, MulAut.conjNormal n k∈L) : Submodule Scalar (Fin d → Scalar) :=
  BinaryCubicStableScalarSubspace.scalarSubspace (D.binaryActiveImage L)
    (D.binaryActiveImage_omega L n hn hL)

/-- Original normality supplies cubic invariance on the same denominator. -/
theorem original_normal_cubic_stable (N : Subgroup Q) [N.Normal]
    (n : Q) (k : D.top.ker) (hk : k∈N.subgroupOf D.top.ker) :
    MulAut.conjNormal n k∈N.subgroupOf D.top.ker := by
  change n*(k : Q)*n⁻¹∈N
  exact (inferInstance : N.Normal).conj_mem (k : Q) hk n

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
