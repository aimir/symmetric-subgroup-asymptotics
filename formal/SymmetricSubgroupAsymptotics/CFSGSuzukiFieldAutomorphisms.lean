import SymmetricSubgroupAsymptotics.CFSGSuzukiZeroFirstBruhat
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! Every automorphism of the original finite field acts entrywise on the
literal Suzuki matrix model. This constructs a faithful actual subgroup
of model automorphisms; identifying all outer automorphisms with this
subgroup is a separate structural obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiFieldAutomorphisms
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent CFSGSuzukiBruhat

def ambientAut (m : ℕ) (σ : Field m ≃+* Field m) : MulAut (CFSGSuzukiTorus.Ambient m) where
  toFun := Matrix.GeneralLinearGroup.map σ.toRingHom
  invFun := Matrix.GeneralLinearGroup.map σ.symm.toRingHom
  left_inv g := by
    apply Units.ext
    ext i j
    exact σ.symm_apply_apply _
  right_inv g := by
    apply Units.ext
    ext i j
    exact σ.apply_symm_apply _
  map_mul' := map_mul (Matrix.GeneralLinearGroup.map σ.toRingHom)

@[simp] theorem ambientAut_entry (m : ℕ) (σ : Field m ≃+* Field m)
    (g : CFSGSuzukiTorus.Ambient m) (i j : Fin 4) :
    (ambientAut m σ g : CFSG.Models.SuzukiConstruction.Mat m) i j=
      σ ((g : CFSG.Models.SuzukiConstruction.Mat m) i j) := rfl

@[simp] theorem ambientAut_unipotent (m : ℕ) (σ : Field m ≃+* Field m) (a b : Field m) :
    ambientAut m σ (unipotentElement m a b)=unipotentElement m (σ a) (σ b) := by
  apply Units.ext
  ext i j
  rw [ambientAut_entry]
  fin_cases i <;> fin_cases j <;>
    simp [unipotentElement_coe,CFSG.Models.SuzukiConstruction.unipotent,map_add,map_mul,map_pow]

@[simp] theorem ambientAut_weyl (m : ℕ) (σ : Field m ≃+* Field m) :
    ambientAut m σ (weylElement m)=weylElement m := by
  apply Units.ext
  ext i j
  rw [ambientAut_entry]
  fin_cases i <;> fin_cases j <;>
    simp [weylElement_coe,CFSG.Models.SuzukiConstruction.weyl]

theorem ambientAut_mem_model (m : ℕ) (σ : Field m ≃+* Field m)
    (g : CFSGSuzukiTorus.Ambient m) (hg : g∈CFSG.Models.SuzukiConstruction.subgroup m) :
    ambientAut m σ g∈CFSG.Models.SuzukiConstruction.subgroup m := by
  have hle : CFSG.Models.SuzukiConstruction.subgroup m≤
      (CFSG.Models.SuzukiConstruction.subgroup m).comap (ambientAut m σ).toMonoidHom := by
    apply model_le_of_unipotent_weyl m
    · rintro u ⟨a,b,rfl⟩
      change ambientAut m σ (unipotentElement m a b)∈CFSG.Models.SuzukiConstruction.subgroup m
      rw [ambientAut_unipotent]
      exact unipotentElement_mem_model m _ _
    · change ambientAut m σ (weylElement m)∈CFSG.Models.SuzukiConstruction.subgroup m
      rw [ambientAut_weyl]
      exact weylElement_mem_model m
  exact hle hg

/-- The original model is preserved in both directions, not merely
mapped into a group of the same order. -/
def modelAut (m : ℕ) (σ : Field m ≃+* Field m) : MulAut (CFSG.Models.Suzuki m) where
  toFun g := ⟨ambientAut m σ g.val,ambientAut_mem_model m σ g.val g.property⟩
  invFun g := ⟨ambientAut m σ.symm g.val,ambientAut_mem_model m σ.symm g.val g.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact σ.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact σ.apply_symm_apply _
  map_mul' g h := Subtype.ext (map_mul (ambientAut m σ) g.val h.val)

@[simp] theorem modelAut_entry (m : ℕ) (σ : Field m ≃+* Field m)
    (g : CFSG.Models.Suzuki m) (i j : Fin 4) :
    ((modelAut m σ g).val : CFSG.Models.SuzukiConstruction.Mat m) i j=
      σ ((g.val : CFSG.Models.SuzukiConstruction.Mat m) i j) := rfl

def fieldAutHom (m : ℕ) : (Field m ≃+* Field m)→*MulAut (CFSG.Models.Suzuki m) where
  toFun := modelAut m
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    rfl

theorem fieldAutHom_injective (m : ℕ) : Function.Injective (fieldAutHom m) := by
  intro σ τ he
  ext a
  let g : CFSG.Models.Suzuki m :=
    ⟨unipotentElement m a 0,unipotentElement_mem_model m a 0⟩
  have hh := congrArg (fun f : MulAut (CFSG.Models.Suzuki m) =>
    ((f g).val : CFSG.Models.SuzukiConstruction.Mat m) 1 0) he
  exact hh

theorem card_fieldAut_image (m : ℕ) : Nat.card (fieldAutHom m).range=2*m+1 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (fieldAutHom_injective m)).toEquiv.symm]
  exact CFSGFiniteFieldAutomorphisms.card_galoisField_ringAut 2 (2*m+1) (by omega)

end SymmetricSubgroupAsymptotics.CFSGSuzukiFieldAutomorphisms
