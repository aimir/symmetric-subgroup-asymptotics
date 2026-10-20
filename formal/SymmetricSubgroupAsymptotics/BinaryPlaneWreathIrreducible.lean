import SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv
import SymmetricSubgroupAsymptotics.PermutationalWreathAffineCoordinates
import SymmetricSubgroupAsymptotics.FunctionBlockProjectionIrreducibility

/-! Independent local order-three binary-plane actions and a transitive
actual block image force irreducibility on all binary translation blocks.
The actual block lifts may carry arbitrary local linear maps. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathIrreducible

open BinaryPlanePermutationAffineEquiv

abbrev V := Multiplicative Plane
abbrev localAction := LinearSemidirectCoprimeSocleBounds.linearAction (MonoidHom.id Linear)

def singer : Linear where
  toFun v := ![v 1,v 0+v 1]
  invFun v := ![v 0+v 1,v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem singer_projection : ∀ v : Plane, singer v + (singer^2) v = v := by
  decide +kernel

theorem singer_nonzero_orbit : ∀ v w : Plane, v ≠ 0 → w ≠ 0 →
    ∃ n : Fin 3, (singer^n.val) v = w := by
  decide +kernel

abbrev Singer := Subgroup.zpowers singer
abbrev singerAction : Singer →* MulAut V := localAction.comp Singer.subtype

theorem singer_irreducible : IrreducibleAbelianSemidirect.Irreducible singerAction := by
  intro S hS
  by_cases hSb : S = ⊥
  · exact Or.inl hSb
  right
  obtain ⟨v,hv,hv1⟩ := S.bot_or_exists_ne_one.resolve_left hSb
  apply top_unique
  intro w _
  by_cases hw : w = 1
  · simpa only [hw] using S.one_mem
  obtain ⟨n,hn⟩ := singer_nonzero_orbit v.toAdd w.toAdd hv1 hw
  have h := hS ⟨singer^n.val,Subgroup.npow_mem_zpowers singer n.val⟩ v hv
  change Multiplicative.ofAdd ((singer^n.val) v.toAdd) ∈ S at h
  rwa [hn] at h

variable {R I : Type} [Group R] [MulAction R I] [DecidableEq I]

abbrev W := PermutationalWreathProduct Linear R I
abbrev action : W (R := R) (I := I) →* MulAut (I → V) :=
  PermutationalWreathAffineCoordinates.action localAction

def localEmbedding (i : I) : Linear →* W (R := R) (I := I) where
  toFun a := ⟨Pi.mulSingle i a,1⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · exact Pi.mulSingle_one i
    · rfl
  map_mul' a b := by
    apply PermutationalWreathProduct.ext
    · funext j
      change (Pi.mulSingle i (a*b) : I → Linear) j =
        (Pi.mulSingle i a : I → Linear) j *
          (Pi.mulSingle i b : I → Linear) ((1 : R)⁻¹ • j)
      rw [inv_one,one_smul]
      exact congrFun (Pi.mulSingle_mul (f := fun _ : I => Linear) i a b) j
    · exact (one_mul 1).symm

theorem action_single (g : W (R := R) (I := I)) (i : I) (v : V) :
    action g (Pi.mulSingle i v) =
      Pi.mulSingle (g.right • i) (localAction (g.left (g.right • i)) v) := by
  funext j
  change localAction (g.left j) ((Pi.mulSingle i v : I → V) (g.right⁻¹ • j)) = _
  by_cases hj : j = g.right • i
  · subst j
    rw [inv_smul_smul,Pi.mulSingle_eq_same,Pi.mulSingle_eq_same]
  · have hn : g.right⁻¹ • j ≠ i := by
      intro h
      apply hj
      calc
        j = g.right • (g.right⁻¹ • j) := (smul_inv_smul _ _).symm
        _ = g.right • i := congrArg (fun z => g.right • z) h
    rw [Pi.mulSingle_eq_of_ne hn,Pi.mulSingle_eq_of_ne hj,map_one]

@[simp] theorem local_action_single (i : I) (a : Linear) (v : V) :
    action (R := R) (localEmbedding i a) (Pi.mulSingle i v) =
      Pi.mulSingle i (localAction a v) := by
  rw [action_single]
  change (Pi.mulSingle ((1 : R) • i)
    (localAction ((Pi.mulSingle i a : I → Linear) ((1 : R) • i)) v) : I → V) =
      Pi.mulSingle i (localAction a v)
  rw [one_smul,Pi.mulSingle_eq_same]

theorem local_projection (i : I) (v : I → V) :
    action (R := R) (localEmbedding i singer) v *
      action (R := R) ((localEmbedding i singer)^2) v = Pi.mulSingle i (v i) := by
  rw [← map_pow]
  funext j
  change localAction ((Pi.mulSingle i singer : I → Linear) j) (v ((1 : R)⁻¹ • j)) *
    localAction ((Pi.mulSingle i (singer^2) : I → Linear) j) (v ((1 : R)⁻¹ • j)) = _
  rw [inv_one,one_smul]
  by_cases hj : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same]
    apply Multiplicative.toAdd.injective
    exact singer_projection _
  · simp only [Pi.mulSingle_eq_of_ne hj,map_one,MulAut.one_apply]
    apply Multiplicative.toAdd.injective
    exact binaryVector_add_self _

variable [Finite I] (C : Subgroup (W (R := R) (I := I)))
  (hloc : ∀ i : I, localEmbedding i singer ∈ C)
  (htrans : ∀ i j : I, ∃ g : C, (g : W (R := R) (I := I)).right • i = j)

abbrev restrictedAction : C →* MulAut (I → V) := action.comp C.subtype

def localLift (i : I) (r : Singer) : C :=
  ⟨localEmbedding i r, (Subgroup.zpowers_le.mpr (hloc i) :
    Subgroup.zpowers singer ≤ C.comap (localEmbedding i)) r.property⟩

include hloc htrans in
theorem irreducible : IrreducibleAbelianSemidirect.Irreducible (restrictedAction C) := by
  apply functionBlock_irreducible_of_projection singerAction (restrictedAction C)
    singer_irreducible (localLift C hloc) ?_ ?_
    (fun i => ⟨localEmbedding i singer,hloc i⟩) ?_
  · intro i r v
    exact local_action_single (R := R) i r v
  · intro i j
    obtain ⟨g,hg⟩ := htrans i j
    refine ⟨g,localAction ((g : W (R := R) (I := I)).left j),?_⟩
    intro v
    change action (g : W (R := R) (I := I)) (Pi.mulSingle i v) = _
    rw [action_single,hg]
  · intro i v
    exact local_projection (R := R) i v

theorem localAction_injective : Function.Injective localAction := by
  intro a b hab
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : MulAut V => (f (Multiplicative.ofAdd v)).toAdd) hab

omit [Finite I] in
theorem action_injective [FaithfulSMul R I] :
    Function.Injective (action (R := R) (I := I)) :=
  PermutationalWreathAffineCoordinates.action_injective localAction localAction_injective

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathIrreducible

end
