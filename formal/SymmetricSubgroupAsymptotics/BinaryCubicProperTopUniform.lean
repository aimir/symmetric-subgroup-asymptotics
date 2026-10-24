import SymmetricSubgroupAsymptotics.BinaryCubicScalarGeneratorTransfer
import SymmetricSubgroupAsymptotics.RepresentationScalarBasisGenerators
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! An actual omega operator makes every binary invariant subspace
scalar closed. In scalar dimension at most two, proper subspaces cost
one generator; an actual cyclic ambient witness handles the top. The
larger group need not act scalar-linearly. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryCubicProperTopUniform
open BinaryQuadraticField (Scalar omega)

variable {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Module Scalar V] [IsScalarTower (ZMod 2) Scalar V]
    [FiniteDimensional Scalar V]
    (rho : Representation (ZMod 2) G V) (H : Subgroup G)
    (tau : Representation Scalar H V)
    (hact : ∀ h : H, ∀ v : V, tau h v = rho (h : G) v)
    (k : H) (hk : ∀ v : V, rho (k : G) v = omega • v)

include hact k hk in
/-- No scalar action of G outside H is asserted. The ambient cyclic
witness is required separately and is not inferred from dimension. -/
theorem uniform_one
    (hdim : Module.finrank Scalar V ≤ 2)
    (hambient : RepresentationGeneratedBy rho 1) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  intro S
  by_cases hS : S = ⊤
  · let inc : S.toRepresentation.IntertwiningMap rho := {
      toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
    have hi : Function.Bijective inc := by
      refine ⟨Subtype.val_injective,?_⟩
      intro v
      refine ⟨⟨v,?_⟩,rfl⟩
      rw [hS]
      trivial
    let e := inc.ofBijective hi
    exact representationGeneratedBy_of_surjective rho S.toRepresentation
      e.symm.toIntertwiningMap e.symm.surjective hambient
  · let restricted : Subrepresentation (rho.comp H.subtype) := {
      toSubmodule := S.toSubmodule
      apply_mem_toSubmodule h _ hv := S.apply_mem_toSubmodule (h : G) hv }
    let Q := BinaryCubicScalarGeneratorTransfer.scalarUpgrade
      (rho.comp H.subtype) tau hact k hk restricted
    have hQ : Q.toSubmodule ≠ ⊤ := by
      intro he
      apply hS
      apply SetLike.ext
      intro v
      change v ∈ S ↔ v ∈ (⊤ : Subrepresentation rho)
      have hv : v ∈ Q.toSubmodule := by rw [he]; trivial
      exact ⟨fun _ => trivial,fun _ => hv⟩
    have hsmall : Module.finrank Scalar Q.toSubmodule ≤ 1 := by
      have hlt := Submodule.finrank_lt hQ
      omega
    let rhoQ := Q.toRepresentation
    let rhoQ2 : Representation (ZMod 2) H Q.toSubmodule := {
      toFun h := (rhoQ h).restrictScalars (ZMod 2)
      map_one' := by
        apply LinearMap.ext
        intro v
        exact congrArg (fun f : Module.End Scalar Q.toSubmodule => f v) rhoQ.map_one
      map_mul' g h := by
        apply LinearMap.ext
        intro v
        exact congrArg (fun f : Module.End Scalar Q.toSubmodule => f v) (rhoQ.map_mul g h) }
    have hq : RepresentationGeneratedBy rhoQ 1 :=
      representationGeneratedBy_of_scalar_finrank_le rhoQ hsmall
    have hb : RepresentationGeneratedBy rhoQ2 1 :=
      BinaryCubicScalarGeneratorTransfer.generatedBy
        rhoQ2 rhoQ (fun _ _ => rfl) k
        (fun v => Subtype.ext ((hact k v).trans (hk v))) hq
    let inter : rhoQ2.IntertwiningMap (S.toRepresentation.comp H.subtype) := {
      toLinearMap := {
        toFun v := ⟨v.val,v.property⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        exact Subtype.ext (hact h v) }
    have hsurj : Function.Surjective inter := by
      intro v
      exact ⟨⟨v.val,v.property⟩,rfl⟩
    have hSH := representationGeneratedBy_of_surjective rhoQ2
      (S.toRepresentation.comp H.subtype) inter hsurj hb
    exact RepresentationGeneratedBy.of_comp S.toRepresentation H.subtype hSH

end SymmetricSubgroupAsymptotics.BinaryCubicProperTopUniform
