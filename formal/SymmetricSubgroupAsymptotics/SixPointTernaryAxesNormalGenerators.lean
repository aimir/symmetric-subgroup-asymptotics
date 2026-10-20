import SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles
import SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairDiagonalUniform

/-! Sum and difference coordinates give two faithful affine-line axes for
the scalar-and-swap ternary action on two blocks. Every actual subgroup
of its six-point image is a surjective image of an actual subgroup of
S3 × S3, with both coordinate maps retained. Hence it has all-normal
bound two. No bound is inherited from an ambient overgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators

open SemidirectProduct
abbrev Local := TernaryLocalWreathNormalGenerators.Local
abbrev Model := Local × Local

abbrev translation : Local := TernaryLocalWreathNormalGenerators.localTranslation
abbrev reflection : Local := TernaryLocalWreathNormalGenerators.localReflection

def sign (g : Local) : ZMod 3 := if g.right = 1 then 1 else -1

def firstOffset (g : Model) : ZMod 3 := 2 * (g.1.left.toAdd + g.2.left.toAdd)
def secondOffset (g : Model) : ZMod 3 := 2 * (g.1.left.toAdd - g.2.left.toAdd)

def pointChart : ZMod 3 ⊕ ZMod 3 ≃ Fin 6 where
  toFun
    | .inl x => (#[0,2,4] : Array (Fin 6))[x.val]!
    | .inr x => (#[1,3,5] : Array (Fin 6))[x.val]!
  invFun := ![.inl 0, .inr 0, .inl 1, .inr 1, .inl 2, .inr 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rawAction (g : Model) : ZMod 3 ⊕ ZMod 3 → ZMod 3 ⊕ ZMod 3
  | .inl x => if sign g.1 = sign g.2 then
      .inl (firstOffset g + sign g.1 * x) else .inr (secondOffset g + sign g.1 * x)
  | .inr x => if sign g.1 = sign g.2 then
      .inr (secondOffset g + sign g.1 * x) else .inl (firstOffset g + sign g.1 * x)

def rawPermutation (g : Model) : Equiv.Perm (ZMod 3 ⊕ ZMod 3) where
  toFun := rawAction g
  invFun := rawAction g⁻¹
  left_inv := by
    rcases g with ⟨⟨u,a⟩,⟨v,b⟩⟩
    intro x
    revert u a v b x
    decide +kernel
  right_inv := by
    rcases g with ⟨⟨u,a⟩,⟨v,b⟩⟩
    intro x
    revert u a v b x
    decide +kernel

def rawHom : Model →* Equiv.Perm (ZMod 3 ⊕ ZMod 3) where
  toFun := rawPermutation
  map_one' := by apply Equiv.ext; intro x; revert x; decide +kernel
  map_mul' := by
    rintro ⟨⟨u,a⟩,⟨v,b⟩⟩ ⟨⟨w,c⟩,⟨z,d⟩⟩
    apply Equiv.ext
    intro x
    revert u a v b w c z d x
    decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 6) :=
  pointChart.permCongrHom.toMonoidHom.comp rawHom

def localChart : ZMod 3 ≃ Fin 3 := (ZMod.finEquiv 3).symm.toEquiv

def localAction : Local →* Equiv.Perm (Fin 3) :=
  localChart.permCongrHom.toMonoidHom.comp SixPairLocalWreathSocles.localAction

theorem localAction_injective : Function.Injective localAction := by
  have h : ∀ g h : Local, localAction g = localAction h → g = h := by
    rintro ⟨u,a⟩ ⟨v,b⟩
    revert u a v b
    decide +kernel
  exact h

/-- The retained coordinates are jointly faithful on every actual subgroup
of the two-axis model, including all diagonal and offset correlations. -/
theorem subgroup_normal_generating_pairs (K : Subgroup Model) :
    ∀ N : Subgroup K, N.Normal →
      ∃ x : Fin 2 → K, Subgroup.normalClosure (Set.range x) = N := by
  let f : K →* Equiv.Perm (Fin 3) :=
    localAction.comp ((MonoidHom.fst Local Local).comp K.subtype)
  let g : K →* Equiv.Perm (Fin 3) :=
    localAction.comp ((MonoidHom.snd Local Local).comp K.subtype)
  apply SymmetricThreeSubgroupNormalGenerators.normal_generating_pairs_of_pair f g
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact localAction_injective (congrArg Prod.fst h)
  · exact localAction_injective (congrArg Prod.snd h)

/-- Pull back the actual image subgroup before taking any normal quotient.
Surjectivity transfers its two coordinate generators to the original P. -/
theorem normal_generating_pairs (P : Subgroup (Equiv.Perm (Fin 6)))
    (hle : P ≤ literalAction.range) :
    ∀ N : Subgroup P, N.Normal →
      ∃ x : Fin 2 → P, Subgroup.normalClosure (Set.range x) = N := by
  let K := P.comap literalAction
  let pi : K →* P := (literalAction.comp K.subtype).codRestrict P (fun x => x.2)
  have hpi : Function.Surjective pi := by
    intro p
    obtain ⟨g,hg⟩ := hle p.2
    exact ⟨⟨g,by change literalAction g ∈ P; rw [hg]; exact p.2⟩,Subtype.ext hg⟩
  exact normal_generating_tuples_of_surjective pi hpi
    (subgroup_normal_generating_pairs K)

theorem normalGen_le (P : Subgroup (Equiv.Perm (Fin 6)))
    (hle : P ≤ literalAction.range) (N : Subgroup P) [N.Normal] :
    MarkedC4.normalGen N ≤ 2 := by
  obtain ⟨x,hx⟩ := normal_generating_pairs P hle N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle_of_original_natural
    {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6)) (hle : F.top.range ≤ literalAction.range)
    (huniform : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 1)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (F.uniform_pair_action_of_original 1 huniform) ?_ N
  intro L hL
  letI := hL
  exact normalGen_le F.top.range hle L

end SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators

end
