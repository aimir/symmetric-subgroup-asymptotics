import SymmetricSubgroupAsymptotics.BinaryPairFrameSquareCarries
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry12
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry13
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry14

/-! The Heisenberg carry certificates apply to the actual original pair
lifts. Every row denominator is the value of a proved derived word in
those same lifts. No complement or involutory-lift premise occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame.HeisenbergCarries

open BinaryHeisenbergEightSquareCarry

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) (u : Fin 4 → U)
  (hp : ∀ i, F.top (u i) = originalSelected i)

def actualOffsets : Offsets := fun j =>
  F.offset (u ((finProdFinEquiv (m := 4) (n := 8)).symm j).1)
    ((finProdFinEquiv (m := 4) (n := 8)).symm j).2

theorem unflatten_actualOffsets :
    unflatten (actualOffsets F u) = fun i => F.offset (u i) := by
  ext i j
  change F.offset (u ((finProdFinEquiv (m := 4) (n := 8)).symm
      (finProdFinEquiv (i, j))).1)
    ((finProdFinEquiv (m := 4) (n := 8)).symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

include hp

theorem lift_top_square (i : Fin 4) : (F.top (u i)) ^ 2 = 1 := by
  rw [hp]
  apply Equiv.ext
  exact originalSelected_involution i

def actualRelator (r : Fin 11) : F.top.ker :=
  ⟨(relators r).eval u, by
    change F.top ((relators r).eval u) = 1
    rw [DerivedGeneratorWord.map_eval]
    rw [show (fun i => F.top (u i)) = originalSelected from funext hp]
    exact relators_top r⟩

theorem actualRelator_mem_commutator (r : Fin 11) :
    (actualRelator F u hp r : U) ∈ commutator U :=
  (relators r).eval_mem_commutator u

theorem squareMap_actualOffsets (i : Fin 4) :
    squareMap i (actualOffsets F u) =
      F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) := by
  change BinarySignedOffsetWord.offset originalSelected [(i, true), (i, true)]
    (unflatten (actualOffsets F u)) = _
  rw [unflatten_actualOffsets, BinarySignedOffsetWord.offset_original F u originalSelected hp]
  change F.offset (BinarySignedOffsetWord.eval u [(i, true), (i, true)]) =
    F.offset (u i ^ 2)
  congr 1

theorem relatorMap_actualOffsets (r : Fin 11) :
    relatorMap r (actualOffsets F u) = F.bits (actualRelator F u hp r) := by
  change BinarySignedOffsetWord.offset originalSelected
    (BinarySignedOffsetWord.ofDerived (relators r)) (unflatten (actualOffsets F u)) = _
  rw [unflatten_actualOffsets, BinarySignedOffsetWord.offset_original F u originalSelected hp,
    BinarySignedOffsetWord.eval_ofDerived]
  rfl

private theorem squares_of_certificate
    (K R : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hcarry : ∀ x : Offsets, (∀ i, squareMap i x ∈ K) →
      (∀ r, relatorMap r x ∈ R) → ∀ i, squareMap i x ∈ R)
    (hK : F.kernelSpace = K)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) ∈ R := by
  have hsquare (i : Fin 4) : squareMap i (actualOffsets F u) ∈ K := by
    rw [squareMap_actualOffsets F u hp, ← hK]
    exact ⟨Additive.ofMul _, rfl⟩
  have hrelator (r : Fin 11) : relatorMap r (actualOffsets F u) ∈ R := by
    rw [relatorMap_actualOffsets F u hp]
    exact hderived _ (actualRelator_mem_commutator F u hp r)
  intro i
  rw [← squareMap_actualOffsets F u hp]
  exact hcarry _ hsquare hrelator i

theorem square_carries12 (hK : F.kernelSpace = K12)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R12) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) ∈ R12 :=
  squares_of_certificate F u hp K12 R12 Case12.square_carry hK hderived

theorem square_carries13 (hK : F.kernelSpace = K13)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R13) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) ∈ R13 :=
  squares_of_certificate F u hp K13 R13 Case13.square_carry hK hderived

theorem square_carries14 (hK : F.kernelSpace = K14)
    (hderived : ∀ k : F.top.ker, (k : U) ∈ commutator U → F.bits k ∈ R14) :
    ∀ i, F.bits (F.carrySquare (u i) (lift_top_square F u hp i)) ∈ R14 :=
  squares_of_certificate F u hp K14 R14 Case14.square_carry hK hderived

end SymmetricSubgroupAsymptotics.BinaryPairFrame.HeisenbergCarries
