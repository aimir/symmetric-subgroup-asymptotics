import SymmetricSubgroupAsymptotics.RepresentationElementHead
import SymmetricSubgroupAsymptotics.PGroupSemiregularElement
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Heads of actual permutation subrepresentations

For a specified element, its fixed functions descend to the quotient by
its actual cyclic orbits. The invariant-form head under the entire acting
group is bounded by this fixed-space dimension, by the annihilator argument
in `RepresentationElementHead`. In particular a nontrivial transitive
p-group action gives the degree / p bound for every actual subrepresentation.
Neither faithfulness nor finiteness of the acting group is required here.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (k G X : Type*) [Field k] [Group G] [MulAction G X]

/-- The original permutation action on functions, with the inverse needed
for a left representation. No orbit labels or new ambient action are chosen. -/
def permutationFunctionRepresentation : Representation k G (X → k) where
  toFun g := {
    toFun f x := f (g⁻¹ • x)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext x
    change f ((1 : G)⁻¹ • x) = f x
    simp only [inv_one, one_smul]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    funext x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

@[simp] theorem permutationFunctionRepresentation_apply (g : G) (f : X → k) (x : X) :
    permutationFunctionRepresentation k G X g f x = f (g⁻¹ • x) := rfl

variable {k G X}

/-- Fixedness for one actual element propagates to every element of its
cyclic subgroup, retaining the original action on the original points. -/
theorem permutationElementFixed_apply_smul (g : G)
    (f : representationElementFixedSpace (permutationFunctionRepresentation k G X) g)
    (a : Subgroup.zpowers g) (x : X) : f.1 (a • x) = f.1 x := by
  let S : Subgroup G := {
    carrier := {a | ∀ x : X, f.1 (a • x) = f.1 x}
    one_mem' := by intro x; rw [one_smul]
    mul_mem' := by
      intro a b ha hb x
      rw [mul_smul, ha, hb]
    inv_mem' := by
      intro a ha x
      have h := (ha (a⁻¹ • x)).symm
      simpa only [smul_inv_smul] using h }
  have hg : g ∈ S := by
    intro x
    have h := congrFun ((mem_representationElementFixedSpace _ _ _).mp f.property) (g • x)
    change f.1 (g⁻¹ • (g • x)) = f.1 (g • x) at h
    simpa only [inv_smul_smul] using h.symm
  exact (Subgroup.zpowers_le.mpr hg) a.property x

/-- A fixed function descends to the quotient by the original cyclic
orbits. This map uses all orbit classes and has no chosen representative data. -/
def permutationElementFixedOrbitEval (g : G) :
    representationElementFixedSpace (permutationFunctionRepresentation k G X) g →ₗ[k]
      (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X → k) where
  toFun f := Quotient.lift (fun x : X => f.1 x) (by
    intro x y h
    obtain ⟨a, ha⟩ := h
    rw [← ha]
    exact permutationElementFixed_apply_smul g f a y)
  map_add' f f' := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  map_smul' c f := by
    funext q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

theorem permutationElementFixedOrbitEval_injective (g : G) :
    Function.Injective (permutationElementFixedOrbitEval (k := k) (X := X) g) := by
  intro f f' h
  apply Subtype.ext
  funext x
  exact congrFun h (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X) x)

/-- Fixed-function dimension is bounded by the number of cyclic orbits.
No characteristic or order assumption is used for this step. -/
theorem permutation_elementFixedSpace_le_cyclicOrbitCount [Finite X] (g : G) :
    Module.finrank k
      (representationElementFixedSpace (permutationFunctionRepresentation k G X) g) ≤
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) := by
  classical
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X)
  have h := (permutationElementFixedOrbitEval (k := k) (X := X) g).finrank_le_finrank_of_injective
    (permutationElementFixedOrbitEval_injective g)
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h

/-- The invariant-form head is taken under the entire original acting
group, even though the ambient fixed-space estimate uses one actual element. -/
theorem permutation_subrepresentationHead_le_cyclicOrbitCount [Finite X]
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) (g : G) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) := by
  letI := Fintype.ofFinite X
  exact (subrepresentationHead_le_ambient_elementFixedSpace
    (permutationFunctionRepresentation k G X) M g).trans
      (permutation_elementFixedSpace_le_cyclicOrbitCount g)

/-- The same statement for actual prime-valued invariant characters. -/
theorem permutation_subrepresentationCharacterHead_le_cyclicOrbitCount
    {p : ℕ} [Fact p.Prime] [Finite X]
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X)) (g : G) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) := by
  letI := Fintype.ofFinite X
  exact (subrepresentationCharacterHead_le_ambient_elementFixedSpace
    (permutationFunctionRepresentation (ZMod p) G X) M g).trans
      (permutation_elementFixedSpace_le_cyclicOrbitCount g)

/-- A nontrivial transitive p-group action has a semiregular element in
its faithful permutation image. The actual lift bounds the head of every
original permutation subrepresentation by degree / p. -/
theorem pGroup_permutationSubrepresentationHead_le_div
    {p : ℕ} [Fact p.Prime] [Finite X] [Nontrivial X]
    [MulAction.IsPretransitive G X] (hG : IsPGroup p G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
        Nat.card X / p := by
  obtain ⟨g, _, _, _, hcount⟩ := pGroup_exists_semiregular_element (X := X) hG
  exact (permutation_subrepresentationHead_le_cyclicOrbitCount M g).trans_eq hcount

/-- In particular p = 2 controls the entire-group invariant character
head of the original correlated pair kernel, once installed as an actual
subrepresentation of the function permutation module. -/
theorem pGroup_permutationSubrepresentationCharacterHead_le_div
    {p : ℕ} [Fact p.Prime] [Finite X] [Nontrivial X]
    [MulAction.IsPretransitive G X] (hG : IsPGroup p G)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X)) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        Nat.card X / p := by
  obtain ⟨g, _, _, _, hcount⟩ := pGroup_exists_semiregular_element (X := X) hG
  exact (permutation_subrepresentationCharacterHead_le_cyclicOrbitCount M g).trans_eq hcount

end SymmetricSubgroupAsymptotics
