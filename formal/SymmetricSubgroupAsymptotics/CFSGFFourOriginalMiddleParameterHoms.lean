import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords

/-! Additive parameter homomorphisms for the same original F4 roots and
the two literal middle Weyl conjugates. These require no simplicity of
the ordinary F4 projective group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleParameterHoms
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourSerreMatrices CFSGFFourOriginalMiddleWords
variable (K : Type) [Field K] [Finite K] [CharP K 2]
local notation "A" => CartanMatrix.F₄

def sourceRootHom (neg : Bool) (i : Fin 4) : Multiplicative K →* Model A K where
  toFun t := modelRoot A K neg i t.toAdd
  map_one' := by
    change modelRoot A K neg i 0=1
    apply rawHom_injective K
    rw [rawHom_root,map_one (rawHom K)]
    exact canonicalRoot_zero realizationData K neg i
  map_mul' a b := by
    change modelRoot A K neg i (a.toAdd+b.toAdd)=
      modelRoot A K neg i a.toAdd*modelRoot A K neg i b.toAdd
    apply rawHom_injective K
    rw [map_mul (rawHom K),rawHom_root,rawHom_root,rawHom_root]
    exact (canonicalRoot_add realizationData K neg i a.toAdd b.toAdd).symm

theorem sourceRootHom_apply (neg : Bool) (i : Fin 4) (t : Multiplicative K) :
    sourceRootHom K neg i t=modelRoot A K neg i t.toAdd := rfl

theorem source_root_add (neg : Bool) (i : Fin 4) (a b : K) :
    modelRoot A K neg i (a+b)=modelRoot A K neg i a*modelRoot A K neg i b :=
  (sourceRootHom K neg i).map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

theorem source_root_zero (neg : Bool) (i : Fin 4) : modelRoot A K neg i 0=1 :=
  (sourceRootHom K neg i).map_one

def middleLongHom : Multiplicative K →* Model A K :=
  (MulAut.conj (weyl K 1)).toMonoidHom.comp (sourceRootHom K false 2)

def middleShortHom : Multiplicative K →* Model A K :=
  (MulAut.conj (weyl K 2)).toMonoidHom.comp (sourceRootHom K false 1)

theorem middleLongHom_apply (t : Multiplicative K) :
    middleLongHom K t=middleLong K t.toAdd := rfl

theorem middleShortHom_apply (t : Multiplicative K) :
    middleShortHom K t=middleShort K t.toAdd := rfl

theorem middleLong_add (a b : K) : middleLong K (a+b)=middleLong K a*middleLong K b :=
  (middleLongHom K).map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

theorem middleShort_add (a b : K) : middleShort K (a+b)=middleShort K a*middleShort K b :=
  (middleShortHom K).map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleParameterHoms
