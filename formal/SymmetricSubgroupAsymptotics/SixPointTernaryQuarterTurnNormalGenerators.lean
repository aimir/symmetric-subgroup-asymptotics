import SymmetricSubgroupAsymptotics.TernaryCyclicPermutationSubgroupNormalGenerators
import SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators

/-! A signed quarter-turn on two ternary blocks has cyclic upper image C4.
Every actual subgroup projecting onto that upper group has all-normal
bound two, even with correlated translations and offset block lifts.
The actual six-point image and every original quotient are retained. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPointTernaryQuarterTurnNormalGenerators

open SemidirectProduct LinearSemidirectCoprimeSocleBounds
abbrev Upper := Multiplicative (ZMod 4)
abbrev Vector := Fin 2 → ZMod 3

def gen : Upper := Multiplicative.ofAdd 1

def blocks : Upper →* Equiv.Perm (Fin 2) where
  toFun g := if g.toAdd.val % 2 = 0 then 1 else Equiv.swap 0 1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def coefficient (g : Upper) : Fin 2 → ZMod 3 :=
  (#[![1,1], ![1,2], ![2,2], ![2,1]] : Array (Fin 2 → ZMod 3))[g.toAdd.val]!

theorem coefficient_one : ∀ i, coefficient 1 i = 1 := by decide +kernel

theorem coefficient_mul : ∀ g h i,
    coefficient (g*h) i = coefficient g i * coefficient h (blocks g⁻¹ i) := by
  decide +kernel

abbrev linearAction := TernaryMonomialCocycle.linearAction
  blocks coefficient coefficient_one coefficient_mul
abbrev Model := LinearSemidirectCoprimeSocleBounds.Model linearAction

def rawAction (g : Model) : ZMod 3 ⊕ ZMod 3 → ZMod 3 ⊕ ZMod 3
  | .inl x => if g.right.toAdd.val % 2 = 0 then
      .inl (g.left.toAdd 0 + coefficient g.right 0 * x) else
      .inr (g.left.toAdd 1 + coefficient g.right 1 * x)
  | .inr x => if g.right.toAdd.val % 2 = 0 then
      .inr (g.left.toAdd 1 + coefficient g.right 1 * x) else
      .inl (g.left.toAdd 0 + coefficient g.right 0 * x)

def rawPermutation (g : Model) : Equiv.Perm (ZMod 3 ⊕ ZMod 3) where
  toFun := rawAction g
  invFun := rawAction g⁻¹
  left_inv := by
    rcases g with ⟨v,c⟩
    intro x
    revert v c x
    decide +kernel
  right_inv := by
    rcases g with ⟨v,c⟩
    intro x
    revert v c x
    decide +kernel

def rawHom : Model →* Equiv.Perm (ZMod 3 ⊕ ZMod 3) where
  toFun := rawPermutation
  map_one' := by apply Equiv.ext; intro x; revert x; decide +kernel
  map_mul' := by
    rintro ⟨v,c⟩ ⟨w,d⟩
    apply Equiv.ext
    intro x
    revert v c w d x
    decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 6) :=
  SixPointTernaryAxesNormalGenerators.pointChart.permCongrHom.toMonoidHom.comp rawHom

theorem uniform : UniformSubrepresentationGeneratorBound
    (linearRepresentation linearAction) 1 := by
  apply TernaryMonomialOrbitUniform.uniform blocks coefficient
    coefficient_one coefficient_mul gen (fun _ : Fin 1 => (0 : Fin 2))
  intro i
  refine ⟨0,i.val,?_⟩
  revert i
  decide +kernel

/-- The displayed offset lift supplies surjectivity; it need not be a pure
complement element and the translation subgroup need not be full. -/
theorem normal_generating_pairs (P : Subgroup (Equiv.Perm (Fin 6)))
    (hle : P ≤ literalAction.range) (lift : Model)
    (hlift : literalAction lift ∈ P) (hgen : lift.right = gen) :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = N := by
  let K := P.comap literalAction
  let pi : K →* P := (literalAction.comp K.subtype).codRestrict P (fun x => x.2)
  have hpi : Function.Surjective pi := by
    intro p
    obtain ⟨g,hg⟩ := hle p.2
    exact ⟨⟨g,by change literalAction g ∈ P; rw [hg]; exact p.2⟩,Subtype.ext hg⟩
  have hsurj : Function.Surjective
      (LinearSemidirectSubgroupKernelChart.projection linearAction K) := by
    intro c
    refine ⟨⟨lift ^ c.toAdd.val, K.pow_mem hlift _⟩,?_⟩
    change (rightHom : Model →* Upper) (lift ^ c.toAdd.val) = c
    rw [map_pow]
    change lift.right ^ c.toAdd.val = c
    rw [hgen]
    revert c
    decide +kernel
  apply normal_generating_tuples_of_surjective pi hpi ?_
  intro N hN
  letI := hN
  apply exists_normal_generating_tuple_of_normalGen_le N
  apply LinearSemidirectSubgroupFullProjection.normalGen_le linearAction K hsurj 1 1 uniform
  intro L hL
  letI := hL
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic L

theorem normalGen_le (P : Subgroup (Equiv.Perm (Fin 6)))
    (hle : P ≤ literalAction.range) (lift : Model)
    (hlift : literalAction lift ∈ P) (hgen : lift.right = gen)
    (N : Subgroup P) [N.Normal] : MarkedC4.normalGen N ≤ 2 := by
  obtain ⟨x,hx⟩ := normal_generating_pairs P hle lift hlift hgen N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle_of_original_natural
    {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6)) (hle : F.top.range ≤ literalAction.range)
    (lift : Model) (hlift : literalAction lift ∈ F.top.range) (hgen : lift.right = gen)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (F.uniform_pair_action_of_original 1 huniform) ?_ N
  intro L hL
  letI := hL
  exact normalGen_le F.top.range hle lift hlift hgen L

end SymmetricSubgroupAsymptotics.SixPointTernaryQuarterTurnNormalGenerators

end
