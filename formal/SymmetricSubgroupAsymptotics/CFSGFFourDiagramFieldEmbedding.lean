import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist

/-! Literal entrywise field embeddings intertwine diagram twists.
An identity-field diagram-fixed matrix over F maps to a genuinely
sigma-diagram-fixed matrix over K when sigma fixes the image of F.
This assertion concerns matrices and injective maps, not recognition of
fixed groups or extension of finite-field centralizer identities. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourDiagramFieldEmbedding
open CFSGSerreQuadraticDiagramFieldTwist
variable {I F K : Type*} [Fintype I] [DecidableEq I] [Field F] [Field K]

def unitsFieldMap (iota : F→+*K) : (Matrix I I F)ˣ→*(Matrix I I K)ˣ :=
  Units.map (iota.mapMatrix : Matrix I I F→+*Matrix I I K).toMonoidHom

theorem unitsFieldMap_entry (iota : F→+*K) (u : (Matrix I I F)ˣ) (i j : I) :
    (unitsFieldMap iota u : Matrix I I K) i j=iota ((u : Matrix I I F) i j) := rfl

theorem unitsFieldMap_injective (iota : F→+*K) :
    Function.Injective (unitsFieldMap (I:=I) iota) := by
  intro u v he
  apply Units.ext
  ext i j
  apply iota.injective
  have hv := congrArg (fun a : (Matrix I I K)ˣ=>(a : Matrix I I K) i j) he
  exact hv

theorem twist_unitsFieldMap (e : Equiv.Perm I) (iota : F→+*K) (sigma : K≃+*K)
    (hfix : ∀a,sigma (iota a)=iota a) (u : (Matrix I I F)ˣ) :
    unitTwist e K sigma (unitsFieldMap iota u)=
      unitsFieldMap iota (unitTwist e F (RingEquiv.refl F) u) := by
  apply Units.ext
  ext i j
  change sigma (iota ((u : Matrix I I F) (e.symm i) (e.symm j)))=
    iota ((u : Matrix I I F) (e.symm i) (e.symm j))
  exact hfix _

theorem fixed_unitsFieldMap (e : Equiv.Perm I) (iota : F→+*K) (sigma : K≃+*K)
    (hfix : ∀a,sigma (iota a)=iota a) (u : (Matrix I I F)ˣ)
    (hu : unitTwist e F (RingEquiv.refl F) u=u) :
    unitTwist e K sigma (unitsFieldMap iota u)=unitsFieldMap iota u := by
  rw [twist_unitsFieldMap e iota sigma hfix,hu]

end SymmetricSubgroupAsymptotics.CFSGFFourDiagramFieldEmbedding
