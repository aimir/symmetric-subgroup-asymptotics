import SymmetricSubgroupAsymptotics.AbelianAutomorphismInversionPairs

/-! The actual kernel of an abelian group's inverse-pair action has
faithful binary coordinates. Its elements act globally as identity or
inversion, so conjugation by the original faithful automorphism group
fixes every kernel element. No scalar-recognition assumption is added. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.InversionPairKernelCoordinates
open AbelianAutomorphismInversionPairs

variable {V H : Type} [CommGroup V] [Group H] (phi : H →* MulAut V)

/-- A faithful additive binary coordinate on the actual inverse-pair kernel. -/
def kernelSign : (pairAction phi).ker →* Multiplicative (ZMod 2) where
  toFun u := if phi u.val = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by
    change (if phi 1 = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)) = 1
    rw [map_one,if_pos rfl]
  map_mul' u v := by
    change (if phi (u.val*v.val) = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)) =
      (if phi u.val = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)) *
        (if phi v.val = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2))
    by_cases hu : phi u.val = 1
    · simp only [map_mul,hu,one_mul,if_true]
    · by_cases hv : phi v.val = 1
      · simp only [map_mul,hv,mul_one,if_neg hu,if_true]
      · have hu' := (kernel_scalar phi u).resolve_left hu
        have hv' := (kernel_scalar phi v).resolve_left hv
        have hprod : phi (u.val*v.val) = 1 := by
          rw [map_mul,hu',hv']
          apply MulEquiv.ext
          intro w
          exact inv_inv w
        rw [hprod,if_pos rfl,if_neg hu,if_neg hv]
        change (0 : ZMod 2) = 1+1
        decide

theorem kernelSign_injective (hphi : Function.Injective phi) :
    Function.Injective (kernelSign phi) := by
  intro u v he
  apply Subtype.ext
  apply hphi
  change (if phi u.val = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)) =
    (if phi v.val = 1 then 1 else Multiplicative.ofAdd (1 : ZMod 2)) at he
  by_cases hu : phi u.val = 1
  · by_cases hv : phi v.val = 1
    · exact hu.trans hv.symm
    · rw [if_pos hu,if_neg hv] at he
      have hbad : (0 : ZMod 2) = 1 := congrArg Multiplicative.toAdd he
      exact (zero_ne_one hbad).elim
  · by_cases hv : phi v.val = 1
    · rw [if_neg hu,if_pos hv] at he
      have hbad : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd he
      exact (one_ne_zero hbad).elim
    · exact ((kernel_scalar phi u).resolve_left hu).trans
        ((kernel_scalar phi v).resolve_left hv).symm

/-- Identity and inversion are central in the full automorphism group of
an abelian group. Faithfulness transports this to the actual complement. -/
theorem kernel_conjugation (hphi : Function.Injective phi) (h : H)
    (u : (pairAction phi).ker) : MulAut.conjNormal h u = u := by
  apply Subtype.ext
  apply hphi
  change phi (h*u.val*h⁻¹) = phi u.val
  rw [map_mul,map_mul,map_inv]
  rcases kernel_scalar phi u with hu | hu
  · rw [hu,mul_one,mul_inv_cancel]
  · rw [hu]
    have hc : phi h * inversionAut V = inversionAut V * phi h := by
      apply MulEquiv.ext
      intro v
      exact map_inv (phi h) v
    rw [hc,mul_assoc,mul_inv_cancel,mul_one]

theorem kernelSign_conjugation (hphi : Function.Injective phi) (h : H)
    (u : (pairAction phi).ker) :
    kernelSign phi (MulAut.conjNormal h u) = kernelSign phi u :=
  congrArg (kernelSign phi) (kernel_conjugation phi hphi h u)

end SymmetricSubgroupAsymptotics.InversionPairKernelCoordinates
