import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Aut

/-! A Cartan exponent minus one couples two field actions exactly.
The relation is expressed by literal rank-one root words and uses no
power-surjectivity or assumption on the characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRankOneTorusFieldCoupling
variable {K G : Type*} [Field K] [Group G]

def weylWord (Y : Bool → Multiplicative K →* G) (c : Kˣ) : G :=
  Y false (Multiplicative.ofAdd (c:K))*Y true (Multiplicative.ofAdd (-(c:K)⁻¹))*
    Y false (Multiplicative.ofAdd (c:K))

def torusWord (Y : Bool → Multiplicative K →* G) (c : Kˣ) : G :=
  weylWord Y c*(weylWord Y 1)⁻¹

theorem torus_covariance (Y : Bool → Multiplicative K →* G) (f : MulAut G) (tau : RingAut K)
    (hY : ∀ (neg:Bool) (t:K),f (Y neg (Multiplicative.ofAdd t))=
      Y neg (Multiplicative.ofAdd (tau t))) (c : Kˣ) :
    f (torusWord Y c)=torusWord Y (Units.map tau.toMonoidHom c) := by
  simp only [torusWord,weylWord,map_mul,map_inv,hY,map_neg,map_inv₀,map_one,
    Units.coe_map,Units.val_one] <;> rfl

theorem field_eq_of_inverse_torus_action
    (X : Multiplicative K →* G) (hXinj : Function.Injective X)
    (Y : Bool → Multiplicative K →* G)
    (hact : ∀(c:Kˣ) (t:K),torusWord Y c*X (Multiplicative.ofAdd t)*(torusWord Y c)⁻¹=
      X (Multiplicative.ofAdd ((c:K)⁻¹*t)))
    (f : MulAut G) (sigma tau : RingAut K)
    (hX : ∀t:K,f (X (Multiplicative.ofAdd t))=X (Multiplicative.ofAdd (sigma t)))
    (hY : ∀(neg:Bool) (t:K),f (Y neg (Multiplicative.ofAdd t))=
      Y neg (Multiplicative.ofAdd (tau t))) : sigma=tau := by
  have hunit (c:Kˣ) : sigma ((c:K)⁻¹)=tau ((c:K)⁻¹) := by
    have he := congrArg f (hact c 1)
    simp only [map_mul,map_inv,torus_covariance Y f tau hY,hX,map_one,mul_one] at he
    rw [hact] at he
    simp only [mul_one,Units.coe_map] at he
    have hp := congrArg Multiplicative.toAdd (hXinj he)
    change (tau (c:K))⁻¹ = sigma ((c:K)⁻¹) at hp
    exact hp.symm.trans (map_inv₀ tau (c:K)).symm
  apply RingEquiv.ext
  intro t
  by_cases ht : t=0
  · simp only [ht,map_zero]
  · have he := hunit ((Units.mk0 t ht)⁻¹)
    simpa only [Units.val_inv_eq_inv_val,Units.val_mk0,inv_inv] using he

end SymmetricSubgroupAsymptotics.CFSGRankOneTorusFieldCoupling
