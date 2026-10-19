import SymmetricSubgroupAsymptotics.TwoTripleProperUpperModelCovers

/-! A physical two-triple permutation determines its affine local maps from
images of two points in each triple. The finite receipt ranges over the fixed
six-point permutation domain, rather than over any subgroup or normal lattice. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTriplePhysicalPermutationCover
open SemidirectProduct
open TwoTripleFullUpperForcesFullWreath

/-- Block zero is the odd triple, agreeing with the published wreath chart. -/
def point (i : Fin 2) (x : ZMod 3) : Fin 6 :=
  if i = 0 then ⟨2*x.val+1, by have hx := x.val_lt; omega⟩ else ⟨2*x.val, by have hx := x.val_lt; omega⟩

def block (x : Fin 6) : Fin 2 := if x.val % 2 = 1 then 0 else 1

def coordinate (x : Fin 6) : ZMod 3 := (x.val / 2 : Nat)

def localWitness (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 2))
    (i : Fin 2) : Local :=
  let a := coordinate (p (point (q.symm i) 0))
  let b := coordinate (p (point (q.symm i) 1))
  ⟨Multiplicative.ofAdd a, if b-a = 1 then 1 else C2Wreath.gen⟩

def witness (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 2)) : Model :=
  ⟨(localWitness p q 0,localWitness p q 1), if q 0 = 0 then 1 else C2Wreath.gen⟩

private theorem point_receipt : ∀ (p : Equiv.Perm (Fin 6))
    (q : Equiv.Perm (Fin 2)),
    (∀ x : Fin 6, block (p x) = q (block x)) →
    ∀ x : Fin 6, SixPairLocalWreathSocles.literalAction (witness p q) x = p x := by
  decide +kernel

theorem cover (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 2))
    (h : ∀ x : Fin 6, block (p x) = q (block x)) :
    p ∈ SixPairLocalWreathSocles.literalAction.range := by
  exact ⟨witness p q,Equiv.ext (point_receipt p q h)⟩

end SymmetricSubgroupAsymptotics.TwoTriplePhysicalPermutationCover
