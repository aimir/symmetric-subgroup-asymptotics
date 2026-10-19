import SymmetricSubgroupAsymptotics.TwoTripleBinaryUpperRecognition
import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform

/-! The actual eight-element signed upper acts on the two ternary local
translations. Its nonzero vectors and nonzero dual forms have stabilizer
at most two. These are fixed 2-dimensional operator receipts, not a list
of subgroups or original normal denominators. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoTripleSignedUpperLinearAction
abbrev Upper := TwoTripleBinaryUpperRecognition.Upper
abbrev Binary := Multiplicative (ZMod 2)
abbrev Vector := Fin 2 → ZMod 3

private def coordinates : Upper ≃ (Binary × Binary) × Binary where
  toFun g := (g.left,g.right)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance upperFintype : Fintype Upper :=
  Fintype.ofEquiv ((Binary × Binary) × Binary) coordinates.symm
local instance upperDecidableEq : DecidableEq Upper := fun a b =>
  decidable_of_iff (coordinates a=coordinates b) coordinates.injective.eq_iff

def blocks : Upper →* Equiv.Perm (Fin 2) where
  toFun g := if g.right=1 then 1 else Equiv.swap 0 1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def sign (b : Binary) : ZMod 3 := if b=1 then 1 else -1

def coefficient (g : Upper) (i : Fin 2) : ZMod 3 :=
  if i=0 then sign g.left.1 else sign g.left.2

theorem coefficient_one : ∀ i, coefficient 1 i=1 := by decide +kernel

theorem coefficient_mul : ∀ g h i,
    coefficient (g*h) i=coefficient g i*coefficient h (blocks g⁻¹ i) := by
  decide +kernel

abbrev representation : Representation (ZMod 3) Upper Vector :=
  TernaryMonomialOrbitUniform.representation blocks coefficient coefficient_one coefficient_mul

/-- Actual point stabilizers in the local translation plane. -/
theorem nonzero_vector_stabilizer_card : ∀ v : Vector, v≠0 →
    (Finset.univ.filter (fun g : Upper => representation g v=v)).card≤2 := by
  decide +kernel

def pairing (ell v : Vector) : ZMod 3 := ell 0*v 0+ell 1*v 1

/-- Actual dual stabilizers, retaining the original linear form. -/
theorem nonzero_form_stabilizer_card : ∀ ell : Vector, ell≠0 →
    (Finset.univ.filter (fun g : Upper =>
      ∀ v : Vector, pairing ell (representation g v)=pairing ell v)).card≤2 := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TwoTripleSignedUpperLinearAction
