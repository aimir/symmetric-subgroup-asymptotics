import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionActualRoots

/-! The actual coordinate Heisenberg law has the alternating shear
cocycle after the literal substitution v=(b,-a), z=dot(a,b)-2c.
The identities are dimension-uniform and use no division. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergCoordinates

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticStabilizerCoordinates CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K] {m : ℕ}

private theorem dot_add_left (a b c : Fin m → K) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private theorem dot_add_right (a b c : Fin m → K) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private theorem dot_comm (a b : Fin m → K) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

def tailVector (g : Element K m) : Index (m + 1) → K :=
  tailExtend m (Sum.elim g.b (-g.a))

def longParameter (g : Element K m) : K := dot g.a g.b - 2 * g.c

theorem tailVector_one : tailVector (1 : Element K m) = 0 := by
  change tailExtend m (Sum.elim (0 : Fin m → K) (-(0 : Fin m → K))) = 0
  funext i
  rcases i with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [tailExtend]

theorem longParameter_one : longParameter (1 : Element K m) = 0 := by
  change dot (0 : Fin m → K) 0 - 2 * (0 : K) = 0
  simp [dot]

theorem tailVector_mul (g h : Element K m) : tailVector (g * h) = tailVector g + tailVector h := by
  change tailExtend m (Sum.elim (g.b + h.b) (-(g.a + h.a))) =
    tailExtend m (Sum.elim g.b (-g.a)) + tailExtend m (Sum.elim h.b (-h.a))
  funext i
  rcases i with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [tailExtend] <;> ring

theorem tailVector_orthogonal_first (g : Element K m) :
    pairing (m + 1) (Pi.single (Sum.inl (0 : Fin (m + 1))) 1) (tailVector g) = 0 := by
  rw [pairing_pos_basis_left]
  exact tailExtend_neg_zero m _

theorem pairing_tailVectors (g h : Element K m) :
    pairing (m + 1) (tailVector g) (tailVector h) = dot g.a h.b - dot g.b h.a := by
  change pairing (m + 1) (tailExtend m _) (tailExtend m _) = _
  rw [pairing_tailExtend]
  unfold pairing dot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change g.b i * (-h.a i) - (-g.a i) * h.b i = g.a i * h.b i - g.b i * h.a i
  ring

theorem longParameter_mul (g h : Element K m) :
    longParameter (g * h) = longParameter g + longParameter h +
      pairing (m + 1) (tailVector g) (tailVector h) := by
  rw [pairing_tailVectors]
  change dot (g.a + h.a) (g.b + h.b) - 2 * (g.c + h.c + dot g.b h.a) =
    (dot g.a g.b - 2 * g.c) + (dot h.a h.b - 2 * h.c) + (dot g.a h.b - dot g.b h.a)
  rw [dot_add_left, dot_add_right, dot_add_right, dot_comm h.a g.b]
  ring

theorem tailVector_central (c : Multiplicative K) :
    tailVector (central (m := m) c) = 0 := by
  funext i
  rcases i with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [tailVector, tailExtend, central]

theorem longParameter_central (c : Multiplicative K) :
    longParameter (central (m := m) c) = -2 * c.toAdd := by
  change dot 0 0 - 2 * c.toAdd = -2 * c.toAdd
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_sub, neg_mul]

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergCoordinates
