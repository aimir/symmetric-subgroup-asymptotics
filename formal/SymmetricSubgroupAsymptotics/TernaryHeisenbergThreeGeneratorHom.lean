import SymmetricSubgroupAsymptotics.TernaryCubePowerHom
import SymmetricSubgroupAsymptotics.CFSGHeisenbergNormalFormHom
import SymmetricSubgroupAsymptotics.CFSGHeisenbergKernelRigidity
import Mathlib.Algebra.Field.ZMod

/-! Three literal cube-one elements, a central commutator, and its
nontriviality suffice for an actual injective Heisenberg27 homomorphism.
All collecting identities are proved by induction; no group table or
recognition theorem is used. Nontriviality must hold in the SAME target,
in particular in the full central quotient when that is the application. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryHeisenbergThreeGeneratorHom
open CFSGHeisenbergCoordinateGroup TernaryCubePowerHom
variable {G : Type*} [Group G]

theorem collect_left_power (x y z : G) (hyz : Commute y z)
    (hcollect : y*x=x*y*z) (n : ℕ) : y^n*x=x*y^n*z^n := by
  induction n with
  | zero => simp only [pow_zero,one_mul,mul_one]
  | succ n ih =>
    calc
      y^(n+1)*x = y*(y^n*x) := by rw [pow_succ']; group
      _ = y*(x*y^n*z^n) := congrArg (fun g => y*g) ih
      _ = (y*x)*y^n*z^n := by group
      _ = (x*y*z)*y^n*z^n := by rw [hcollect]
      _ = x*y*(z*y^n)*z^n := by group
      _ = x*y*(y^n*z)*z^n := by rw [(hyz.symm.pow_right n).eq]
      _ = x*y^(n+1)*z^(n+1) := by group

theorem collect_powers (x y z : G) (hxz : Commute x z) (hyz : Commute y z)
    (hcollect : y*x=x*y*z) (m n : ℕ) :
    y^n*x^m=x^m*y^n*z^(n*m) := by
  have hs : SemiconjBy (y^n) x (x*z^n) := by
    calc
      y^n*x = x*y^n*z^n := collect_left_power x y z hyz hcollect n
      _ = x*(y^n*z^n) := mul_assoc _ _ _
      _ = x*(z^n*y^n) := congrArg (fun g => x*g) (hyz.pow_pow n n).eq
      _ = (x*z^n)*y^n := (mul_assoc _ _ _).symm
  have hp := (hs.pow_right m).eq
  rw [(hxz.pow_right n).mul_pow m,←pow_mul] at hp
  calc
    y^n*x^m = x^m*(z^(n*m)*y^n) := by simpa only [mul_assoc] using hp
    _ = x^m*(y^n*z^(n*m)) :=
      congrArg (fun g => x^m*g) (hyz.pow_pow n (n*m)).eq.symm
    _ = x^m*y^n*z^(n*m) := (mul_assoc _ _ _).symm

def coordinatePower (x : G) (hx : x^3=1) :
    Multiplicative (Fin 1 → ZMod 3) →* G where
  toFun v := powerHom x hx (Multiplicative.ofAdd (v.toAdd 0))
  map_one' := (powerHom x hx).map_one
  map_mul' _v _w := (powerHom x hx).map_mul _ _

theorem coordinatePower_commute (x z : G) (hx : x^3=1) (hz : z^3=1)
    (hxz : Commute x z) (a : Fin 1 → ZMod 3) (c : ZMod 3) :
    Commute (coordinatePower x hx (Multiplicative.ofAdd a))
      (powerHom z hz (Multiplicative.ofAdd c)) := by
  change Commute (powerHom x hx (Multiplicative.ofAdd (a 0)))
    (powerHom z hz (Multiplicative.ofAdd c))
  rw [powerHom_val,powerHom_val]
  exact hxz.pow_pow _ _

theorem coordinate_collect (x y z : G) (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z)
    (a b : Fin 1 → ZMod 3) :
    coordinatePower y hy (Multiplicative.ofAdd b)*
        coordinatePower x hx (Multiplicative.ofAdd a) =
      coordinatePower x hx (Multiplicative.ofAdd a)*
        coordinatePower y hy (Multiplicative.ofAdd b)*
        powerHom z hz (Multiplicative.ofAdd (dot b a)) := by
  change powerHom y hy (Multiplicative.ofAdd (b 0))*
      powerHom x hx (Multiplicative.ofAdd (a 0)) =
    powerHom x hx (Multiplicative.ofAdd (a 0))*
      powerHom y hy (Multiplicative.ofAdd (b 0))*
      powerHom z hz (Multiplicative.ofAdd (dot b a))
  simp only [powerHom_val x hx (a 0),powerHom_val y hy (b 0)]
  simp only [dot,Fin.sum_univ_one]
  have he : (((b 0).val*(a 0).val : ℕ) : ZMod 3)=b 0*a 0 := by
    rw [Nat.cast_mul,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  rw [←he,powerHom_natCast]
  exact collect_powers x y z hxz hyz hcollect (a 0).val (b 0).val

def hom (x y z : G) (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z) :
    Element (ZMod 3) 1 →* G :=
  CFSGHeisenbergNormalFormHom.coordinateHom
    (coordinatePower x hx) (coordinatePower y hy) (powerHom z hz)
    (coordinatePower_commute x z hx hz hxz)
    (coordinatePower_commute y z hy hz hyz)
    (coordinate_collect x y z hx hy hz hxz hyz hcollect)

theorem hom_central (x y z : G) (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z)
    (c : Multiplicative (ZMod 3)) :
    hom x y z hx hy hz hxz hyz hcollect (central c)=powerHom z hz c :=
  CFSGHeisenbergNormalFormHom.coordinateHom_central
    (coordinatePower x hx) (coordinatePower y hy) (powerHom z hz)
    (coordinatePower_commute x z hx hz hxz)
    (coordinatePower_commute y z hy hz hyz)
    (coordinate_collect x y z hx hy hz hxz hyz hcollect) c

theorem hom_comp_central (x y z : G) (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z) :
    (hom x y z hx hy hz hxz hyz hcollect).comp
      (central (K := ZMod 3) (m := 1))=powerHom z hz := by
  apply MonoidHom.ext
  intro c
  exact hom_central x y z hx hy hz hxz hyz hcollect c

theorem injective_of_central_power (f : Element (ZMod 3) 1 →* G)
    (z : G) (hz : z^3=1) (hne : z≠1)
    (hf : f.comp (central (K := ZMod 3) (m := 1))=powerHom z hz) :
    Function.Injective (fun h : Element (ZMod 3) 1 => f h) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcentral : Function.Injective (fun c : Multiplicative (ZMod 3) =>
      f (central (K := ZMod 3) (m := 1) c)) := by
    intro c d hcd
    exact (powerHom_injective z hz hne)
      ((DFunLike.congr_fun hf c).symm.trans (hcd.trans (DFunLike.congr_fun hf d)))
  exact CFSGHeisenbergKernelRigidity.injective_of_central (K := ZMod 3) (m := 1)
    f hcentral

theorem hom_injective (x y z : G) (hx : x^3=1) (hy : y^3=1) (hz : z^3=1)
    (hxz : Commute x z) (hyz : Commute y z) (hcollect : y*x=x*y*z)
    (hne : z≠1) : Function.Injective
      (fun h : Element (ZMod 3) 1 => hom x y z hx hy hz hxz hyz hcollect h) :=
  injective_of_central_power (hom x y z hx hy hz hxz hyz hcollect) z hz hne
    (hom_comp_central x y z hx hy hz hxz hyz hcollect)

end SymmetricSubgroupAsymptotics.TernaryHeisenbergThreeGeneratorHom
