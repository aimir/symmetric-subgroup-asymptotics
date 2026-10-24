import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralExtensionLayers
import Mathlib.GroupTheory.SemidirectProduct

/-! Literal U and original torus matrices give the actual semidirect
product action inside the SAME Suzuki group.  The central source map
remains injective there; no abstract Borel recognition or central-quotient
faithfulness premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBorelSemidirectHom
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiTorus
open CFSGSuzukiCentralExtensionLayers

def unipotentHom (m : ℕ) : unipotentSubgroup m →* CFSG.Models.Suzuki m :=
  Subgroup.inclusion (unipotentSubgroup_le_model m)

theorem unipotentHom_injective (m : ℕ) : Function.Injective (unipotentHom m) :=
  Subgroup.inclusion_injective _

def torusHom (m : ℕ) : (Field m)ˣ →* CFSG.Models.Suzuki m where
  toFun c := ⟨torusElement m c, torusElement_mem_model m c⟩
  map_one' := Subtype.ext (torusElement_one m)
  map_mul' c d := Subtype.ext (torusElement_mul m c d)

theorem torus_conjugation (m : ℕ) (c : (Field m)ˣ) (u : unipotentSubgroup m) :
    unipotentHom m (torusAutHom m c u) =
      torusHom m c * unipotentHom m u * (torusHom m c)⁻¹ := Subtype.ext rfl

def extensionHom (m : ℕ) :
    unipotentSubgroup m ⋊[torusAutHom m] (Field m)ˣ →* CFSG.Models.Suzuki m :=
  SemidirectProduct.lift (unipotentHom m) (torusHom m)
    (fun c => MonoidHom.ext (fun u => torus_conjugation m c u))

@[simp] theorem extensionHom_inl (m : ℕ) (u : unipotentSubgroup m) :
    extensionHom m (SemidirectProduct.inl u) = unipotentHom m u := by
  simp only [extensionHom, SemidirectProduct.lift_inl]

@[simp] theorem extensionHom_central (m : ℕ) (b : Multiplicative (Field m)) :
    extensionHom m (SemidirectProduct.inl (centralHom m b)) =
      CFSGSuzukiCentralPermutationDegree.centralModelHom m b := by
  rw [extensionHom_inl]
  rfl

theorem extensionHom_central_injective (m : ℕ) :
    Function.Injective (fun b : Multiplicative (Field m) =>
      extensionHom m (SemidirectProduct.inl (centralHom m b))) := by
  intro a b he
  dsimp only at he
  rw [extensionHom_central, extensionHom_central] at he
  exact CFSGSuzukiCentralPermutationDegree.centralModelHom_injective m he

end SymmetricSubgroupAsymptotics.CFSGSuzukiBorelSemidirectHom
