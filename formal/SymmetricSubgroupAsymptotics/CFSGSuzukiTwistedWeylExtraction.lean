import SymmetricSubgroupAsymptotics.CFSGSuzukiOriginalTorusAction
import SymmetricSubgroupAsymptotics.CFSGSuzukiWeylTorus
import Mathlib.Tactic.Group

/-! A word in the original torus and a unipotent times the original Weyl
matrix has nonzero first unipotent parameter. Both second parameters are
retained, and are irrelevant only in the subsequent saturation theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiGeneration
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent

def twistedWeyl (m : ℕ) : CFSGSuzukiTorus.Ambient m :=
  unipotentElement m 1 0*weylElement m

theorem twistedWeyl_torus_commutator (m : ℕ) (c : (Field m)ˣ) :
    ∃ b : Field m,
      ⁅twistedWeyl m*torusElement m c*(twistedWeyl m)⁻¹,torusElement m c⁆=
        unipotentElement m ((c : Field m)+(c : Field m)⁻¹) b := by
  let h := torusElement m c
  let u := unipotentElement m (1 : Field m) 0
  have hy : twistedWeyl m*h*(twistedWeyl m)⁻¹=u*h⁻¹*u⁻¹ := by
    change (u*weylElement m)*h*(u*weylElement m)⁻¹=u*h⁻¹*u⁻¹
    rw [mul_inv_rev]
    have he : weylElement m*h*(weylElement m)⁻¹=h⁻¹ := by
      exact (weyl_torus_conjugation m c).trans (torusElement_inv m c).symm
    calc
      (u*weylElement m)*h*((weylElement m)⁻¹*u⁻¹)=
          u*(weylElement m*h*(weylElement m)⁻¹)*u⁻¹ := by group
      _=u*h⁻¹*u⁻¹ := by rw [he]
  have hw : ⁅twistedWeyl m*h*(twistedWeyl m)⁻¹,h⁆=
      u*(h⁻¹*u⁻¹*h)*u*(h*u⁻¹*h⁻¹) := by
    rw [hy,commutatorElement_def]
    group
  have hi : h⁻¹*u⁻¹*h=unipotentElement m (c : Field m)
      (((c : Field m)⁻¹*theta m ((c : Field m)⁻¹))⁻¹) := by
    change (torusElement m c)⁻¹*(unipotentElement m 1 0)⁻¹*torusElement m c=_
    rw [unipotentElement_inv]
    simp only [map_one,mul_one,zero_add]
    simpa only [torusElement_inv,inv_inv,Units.val_inv_eq_inv_val,mul_one]
      using original_torus_conjugation m c⁻¹ 1 1
  have hj : h*u⁻¹*h⁻¹=unipotentElement m (c : Field m)⁻¹
      (((c : Field m)*theta m (c : Field m))⁻¹) := by
    change torusElement m c*(unipotentElement m 1 0)⁻¹*(torusElement m c)⁻¹=_
    rw [unipotentElement_inv]
    simp only [map_one,mul_one,zero_add]
    rw [original_torus_conjugation]
    simp only [mul_one]
  rw [hw,hi,hj]
  dsimp only [u]
  simp only [unipotentElement_mul]
  have ha : (1 : Field m)+(c : Field m)+1+(c : Field m)⁻¹=
      (c : Field m)+(c : Field m)⁻¹ := by
    rw [add_assoc (1 : Field m) (c : Field m) 1,add_comm (c : Field m) 1,
      ←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  rw [ha]
  exact ⟨_,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGSuzukiGeneration
