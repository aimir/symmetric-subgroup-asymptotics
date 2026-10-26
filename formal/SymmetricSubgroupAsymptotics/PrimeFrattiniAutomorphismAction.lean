import SymmetricSubgroupAsymptotics.AutomorphismQuotientKernelCardinality
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! Every actual automorphism acts on the actual prime-evaluation
quotient. Functoriality supplies the inverse and multiplication laws.
For a finite p-group, the actual action kernel is counted using the
SAME Frattini generating tuple and original Frattini fibres. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismAction

variable (p : ℕ) [Fact p.Prime] (N : Type*) [Group N] [Finite N]

def linearAut (a : MulAut N) :
    PrimeAbelianization p N ≃ₗ[ZMod p] PrimeAbelianization p N where
  toLinearMap := primeAbelianizationMapHom p a.toMonoidHom
  invFun := primeAbelianizationMapHom p a.symm.toMonoidHom
  left_inv v := by
    have hc : a.symm.toMonoidHom.comp a.toMonoidHom=MonoidHom.id N := by
      ext n
      exact a.symm_apply_apply n
    have he := primeAbelianizationMapHom_comp p a.toMonoidHom a.symm.toMonoidHom
    rw [hc,primeAbelianizationMapHom_id] at he
    exact congrArg (fun f : PrimeAbelianization p N →ₗ[ZMod p] PrimeAbelianization p N => f v) he.symm
  right_inv v := by
    have hc : a.toMonoidHom.comp a.symm.toMonoidHom=MonoidHom.id N := by
      ext n
      exact a.apply_symm_apply n
    have he := primeAbelianizationMapHom_comp p a.symm.toMonoidHom a.toMonoidHom
    rw [hc,primeAbelianizationMapHom_id] at he
    exact congrArg (fun f : PrimeAbelianization p N →ₗ[ZMod p] PrimeAbelianization p N => f v) he.symm

theorem linearAut_apply (a : MulAut N) (n : N) :
    linearAut p N a (primeAbelianizationMap p N (Additive.ofMul n))=
      primeAbelianizationMap p N (Additive.ofMul (a n)) :=
  primeAbelianizationMapHom_apply p a.toMonoidHom n

def linearAction : MulAut N →*
    (PrimeAbelianization p N ≃ₗ[ZMod p] PrimeAbelianization p N) where
  toFun := linearAut p N
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change primeAbelianizationMapHom p (1 : MulAut N).toMonoidHom v=v
    simp only [show (1 : MulAut N).toMonoidHom=MonoidHom.id N from rfl,
      primeAbelianizationMapHom_id,LinearMap.id_apply]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    change primeAbelianizationMapHom p (a*b).toMonoidHom v=
      primeAbelianizationMapHom p a.toMonoidHom (primeAbelianizationMapHom p b.toMonoidHom v)
    simp only [show (a*b).toMonoidHom=a.toMonoidHom.comp b.toMonoidHom from rfl,
      primeAbelianizationMapHom_comp,LinearMap.comp_apply]

def groupAction : MulAut N →* MulAut (Multiplicative (PrimeAbelianization p N)) where
  toFun a := ((linearAction p N a).toAddEquiv).toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change linearAction p N 1 v.toAdd=v.toAdd
    rw [(linearAction p N).map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro v
    change linearAction p N (a*b) v.toAdd=
      linearAction p N a (linearAction p N b v.toAdd)
    rw [(linearAction p N).map_mul]
    rfl

theorem groupAction_apply (a : MulAut N) (n : N) :
    groupAction p N a (primeAbelianizationGroupMap p N n)=
      primeAbelianizationGroupMap p N (a n) := by
  change Multiplicative.ofAdd (linearAut p N a
    (primeAbelianizationMap p N (Additive.ofMul n)))=
      Multiplicative.ofAdd (primeAbelianizationMap p N (Additive.ofMul (a n)))
  rw [linearAut_apply]

theorem kernel_card_le_frattini_pow_primeRank (hN : IsPGroup p N) :
    Nat.card (groupAction p N).ker≤(Nat.card (frattini N))^
      Module.finrank (ZMod p) (PrimeCharacters p N) := by
  apply AutomorphismQuotientKernelCardinality.card_le_frattini_pow_primeRank p hN
  intro a n
  have he := DFunLike.congr_fun a.property (primeAbelianizationGroupMap p N n)
  change groupAction p N a.val (primeAbelianizationGroupMap p N n)=
    primeAbelianizationGroupMap p N n at he
  rw [groupAction_apply] at he
  exact he

end SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismAction
