import SymmetricSubgroupAsymptotics.SolubleSocleSemisimple
import SymmetricSubgroupAsymptotics.MarkedC4SocleSurjectiveImage

/-! The inverse images of the factor socles of a finite soluble subdirect
product intersect in exactly its literal socle. The reverse inclusion uses
the actual equivariant embedding into a product of semisimple integral
conjugation modules, retaining arbitrary subdirect correlations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.SolubleSubdirectSocleIntersection

open SolubleSocleConjugationModule

variable {I : Type} (F : I → Type) [∀ i, Group (F i)]
variable {G : Type} [Group G] (f : G →* ∀ i, F i)

def coordinate (i : I) : G →* F i := (Pi.evalMonoidHom F i).comp f

def preimage : Subgroup G :=
  ⨅ i : I, (finiteGroupSocle (F i)).comap (coordinate F f i)

instance preimage_normal : (preimage F f).Normal :=
  Subgroup.normal_iInf_normal (fun _ => inferInstance)

theorem mem_preimage (g : G) :
    g ∈ preimage F f ↔ ∀ i, coordinate F f i g ∈ finiteGroupSocle (F i) := by
  simp only [preimage, Subgroup.mem_iInf, Subgroup.mem_comap]

def projection (i : I) : preimage F f →* finiteGroupSocle (F i) where
  toFun n := ⟨coordinate F f i n.1, (mem_preimage F f n.1).mp n.2 i⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.1 b.1)

theorem preimage_isMulCommutative
    [∀ i, Finite (F i)] [∀ i, IsSolvable (F i)]
    (hf : Function.Injective f) : IsMulCommutative (preimage F f) := by
  apply isMulCommutative_iff.mpr
  intro a b
  apply Subtype.ext
  apply hf
  funext i
  letI : IsMulCommutative (finiteGroupSocle (F i)) := socle_isMulCommutative
  have he := congrArg Subtype.val (mul_comm (projection F f i a) (projection F f i b))
  change coordinate F f i ((a : G) * (b : G)) =
    coordinate F f i ((b : G) * (a : G))
  rw [map_mul, map_mul]
  exact he

section Conjugation

variable [IsMulCommutative (preimage F f)]
variable [∀ i, IsMulCommutative (finiteGroupSocle (F i))]

def projectionIntertwiner (i : I) :
    (representation (preimage F f)).IntertwiningMap
      ((representation (finiteGroupSocle (F i))).comp (coordinate F f i)) where
  toLinearMap := (MonoidHom.toAdditive (projection F f i)).toIntLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change coordinate F f i (g * (v.toMul : G) * g⁻¹) =
      coordinate F f i g * coordinate F f i (v.toMul : G) * (coordinate F f i g)⁻¹
    simp only [map_mul, map_inv]

def moduleEmbedding : (representation (preimage F f)).asModule →ₗ[ℤ[G]]
    ∀ i, Representation.asModule
      ((representation (finiteGroupSocle (F i))).comp (coordinate F f i)) :=
  LinearMap.pi (fun i => Representation.IntertwiningMap.equivLinearMapAsModule
    (representation (preimage F f))
    ((representation (finiteGroupSocle (F i))).comp (coordinate F f i))
    (projectionIntertwiner F f i))

theorem moduleEmbedding_injective (hf : Function.Injective f) :
    Function.Injective (moduleEmbedding F f) := by
  intro x y he
  apply Additive.toMul.injective
  apply Subtype.ext
  apply hf
  funext i
  exact congrArg (fun z => (z.toMul : F i)) (congrFun he i)

end Conjugation

/-- The key reverse inclusion is proved for the actual correlated normal
subgroup, not for an unconstrained product of its coordinate images. -/
theorem preimage_le_socle [Finite I]
    [∀ i, Finite (F i)] [∀ i, IsSolvable (F i)]
    (hf : Function.Injective f)
    (hs : ∀ i, Function.Surjective (coordinate F f i)) :
    preimage F f ≤ finiteGroupSocle G := by
  letI : IsMulCommutative (preimage F f) := preimage_isMulCommutative F f hf
  letI (i : I) : IsMulCommutative (finiteGroupSocle (F i)) := socle_isMulCommutative
  letI (i : I) : IsSemisimpleModule ℤ[G]
      (Representation.asModule
        ((representation (finiteGroupSocle (F i))).comp (coordinate F f i))) := by
    letI : IsSemisimpleModule ℤ[F i]
        (representation (finiteGroupSocle (F i))).asModule := socle_isSemisimple
    exact semisimple_comp (coordinate F f i) (hs i)
      (representation (finiteGroupSocle (F i)))
  let E := moduleEmbedding F f
  letI : IsSemisimpleModule ℤ[G] (representation (preimage F f)).asModule :=
    IsSemisimpleModule.of_injective
      { toFun := E
        map_add' := fun a b => E.map_add a b
        map_smul' := fun r a => E.map_smul r a }
      (moduleEmbedding_injective F f hf)
  exact le_socle_of_semisimple (preimage F f)

theorem preimage_eq_socle [Finite I]
    [∀ i, Finite (F i)] [∀ i, IsSolvable (F i)]
    (hf : Function.Injective f)
    (hs : ∀ i, Function.Surjective (coordinate F f i)) :
    preimage F f = finiteGroupSocle G := by
  apply le_antisymm (preimage_le_socle F f hf hs)
  intro g hg
  apply (mem_preimage F f g).mpr
  intro i
  exact MarkedC4.SocleSurjectiveImage.socle_le_comap (coordinate F f i) (hs i) hg

end SymmetricSubgroupAsymptotics.SolubleSubdirectSocleIntersection
