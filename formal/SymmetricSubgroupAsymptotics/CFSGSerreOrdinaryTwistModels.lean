import SymmetricSubgroupAsymptotics.CFSGSerreForkDiagram
import SymmetricSubgroupAsymptotics.CFSGSerreFieldTwistGraph

/-! The four ordinary twisted constructions in the pinned CFSG models use
actual diagram--Frobenius automorphisms on their original elementary groups.
Their literal generated graph definitions are therefore functional, not
merely surjective correspondences. Exceptional Ree isogenies are separate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwists
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreFieldDiagram

def definingFieldAutomorphism (q : CFSG.PrimePower) (d : ℕ) :
    q.Extension d ≃+* q.Extension d :=
  iterateFrobeniusEquiv (q.Extension d) q.prime q.exponent

@[simp] theorem definingFieldAutomorphism_apply (q : CFSG.PrimePower) (d : ℕ)
    (t : q.Extension d) : definingFieldAutomorphism q d t = t ^ q.order := rfl

def typeAAmbientAction (r : ℕ) (q : CFSG.PrimePower) :
    MulAut (Ambient (CartanMatrix.A r) (q.Extension 2)) :=
  CFSGSerreFieldDiagram.ambientAutomorphism (CartanMatrix.A r) (q.Extension 2) Fin.revPerm
    (typeA_reverse_preserves r) (definingFieldAutomorphism q 2)

def typeDAmbientAction (r : ℕ) (q : CFSG.PrimePower) :
    MulAut (Ambient (CartanMatrix.D r) (q.Extension 2)) :=
  CFSGSerreFieldDiagram.ambientAutomorphism (CartanMatrix.D r) (q.Extension 2) (dPermutation r)
    (d_preserves r) (definingFieldAutomorphism q 2)

def e6AmbientAction (q : CFSG.PrimePower) :
    MulAut (Ambient CartanMatrix.E₆ (q.Extension 2)) :=
  CFSGSerreFieldDiagram.ambientAutomorphism CartanMatrix.E₆ (q.Extension 2) e6Permutation
    e6_preserves (definingFieldAutomorphism q 2)

def trialityAmbientAction (q : CFSG.PrimePower) :
    MulAut (Ambient (CartanMatrix.D 4) (q.Extension 3)) :=
  CFSGSerreFieldDiagram.ambientAutomorphism (CartanMatrix.D 4) (q.Extension 3) trialityPermutation
    triality_preserves (definingFieldAutomorphism q 3)

theorem typeA_mem_twistGraph_iff (r : ℕ) (q : CFSG.PrimePower)
    (gh : Ambient (CartanMatrix.A r) (q.Extension 2) ×
      Ambient (CartanMatrix.A r) (q.Extension 2)) :
    gh ∈ twistGraph (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode
      (fun _ => q.order) ↔
    gh.1 ∈ subgroup (CartanMatrix.A r) (q.Extension 2) ∧
      gh.2 = typeAAmbientAction r q gh.1 := by
  exact CFSGSerreFieldDiagram.mem_twistGraph_iff (CartanMatrix.A r) (q.Extension 2) Fin.revPerm
    (typeA_reverse_preserves r) (definingFieldAutomorphism q 2) q.order
    (definingFieldAutomorphism_apply q 2) gh

theorem typeD_mem_twistGraph_iff (r : ℕ) (q : CFSG.PrimePower)
    (gh : Ambient (CartanMatrix.D r) (q.Extension 2) ×
      Ambient (CartanMatrix.D r) (q.Extension 2)) :
    gh ∈ twistGraph (CartanMatrix.D r) (q.Extension 2) CFSG.Models.dTwist
      (fun _ => q.order) ↔
    gh.1 ∈ subgroup (CartanMatrix.D r) (q.Extension 2) ∧
      gh.2 = typeDAmbientAction r q gh.1 := by
  exact CFSGSerreFieldDiagram.mem_twistGraph_iff (CartanMatrix.D r) (q.Extension 2) (dPermutation r)
    (d_preserves r) (definingFieldAutomorphism q 2) q.order
    (definingFieldAutomorphism_apply q 2) gh

theorem e6_mem_twistGraph_iff (q : CFSG.PrimePower)
    (gh : Ambient CartanMatrix.E₆ (q.Extension 2) × Ambient CartanMatrix.E₆ (q.Extension 2)) :
    gh ∈ twistGraph CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist
      (fun _ => q.order) ↔
    gh.1 ∈ subgroup CartanMatrix.E₆ (q.Extension 2) ∧
      gh.2 = e6AmbientAction q gh.1 := by
  exact CFSGSerreFieldDiagram.mem_twistGraph_iff CartanMatrix.E₆ (q.Extension 2) e6Permutation
    e6_preserves (definingFieldAutomorphism q 2) q.order
    (definingFieldAutomorphism_apply q 2) gh

theorem triality_mem_twistGraph_iff (q : CFSG.PrimePower)
    (gh : Ambient (CartanMatrix.D 4) (q.Extension 3) ×
      Ambient (CartanMatrix.D 4) (q.Extension 3)) :
    gh ∈ twistGraph (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) ↔
    gh.1 ∈ subgroup (CartanMatrix.D 4) (q.Extension 3) ∧
      gh.2 = trialityAmbientAction q gh.1 := by
  exact CFSGSerreFieldDiagram.mem_twistGraph_iff (CartanMatrix.D 4) (q.Extension 3) trialityPermutation
    triality_preserves (definingFieldAutomorphism q 3) q.order
    (definingFieldAutomorphism_apply q 3) gh

def typeAModelAutomorphism (r : ℕ) (q : CFSG.PrimePower) :
    MulAut (Model (CartanMatrix.A r) (q.Extension 2)) :=
  CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.A r) (q.Extension 2) Fin.revPerm
    (typeA_reverse_preserves r) (definingFieldAutomorphism q 2)

def typeDModelAutomorphism (r : ℕ) (q : CFSG.PrimePower) :
    MulAut (Model (CartanMatrix.D r) (q.Extension 2)) :=
  CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D r) (q.Extension 2) (dPermutation r)
    (d_preserves r) (definingFieldAutomorphism q 2)

def e6ModelAutomorphism (q : CFSG.PrimePower) :
    MulAut (Model CartanMatrix.E₆ (q.Extension 2)) :=
  CFSGSerreFieldDiagram.modelAutomorphism CartanMatrix.E₆ (q.Extension 2) e6Permutation
    e6_preserves (definingFieldAutomorphism q 2)

def trialityModelAutomorphism (q : CFSG.PrimePower) :
    MulAut (Model (CartanMatrix.D 4) (q.Extension 3)) :=
  CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D 4) (q.Extension 3) trialityPermutation
    triality_preserves (definingFieldAutomorphism q 3)

end SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwists
