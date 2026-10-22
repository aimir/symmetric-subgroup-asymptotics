import SymmetricSubgroupAsymptotics.CFSGIntegerDominantSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! Actual Cartan connectivity forces every positive dominant root of
the coordinate root system to have FULL support. No exceptional table
or graph-connectivity premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerDominantSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

include hd hs hp ho

theorem coordinate_cartan_induction (p : Fin r→Prop) (i j : Fin r) (hi : p i)
    (hstep : ∀a b,p a→A b a≠0→p b) : p j := by
  have hh := (b₀).induction_on_cartanMatrix (fun a=>p ((s₀).symm a))
    (i:=s₀ i) (j:=s₀ j) (by simpa only [Equiv.symm_apply_apply] using hi) (by
      intro a b ha hab
      apply hstep ((s₀).symm a) ((s₀).symm b) ha
      rw [←coordinate_cartan A hd hs hp ho ((s₀).symm b) ((s₀).symm a)]
      simpa only [Equiv.apply_symm_apply] using hab)
  simpa only [Equiv.symm_apply_apply] using hh

theorem dominant_positive_root_full_support (k : Roots A) (hk : ∀i,0≤k.val i)
    (hdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    ∀i,0<k.val i := by
  intro i
  by_contra hn
  have hzero : k.val i=0 := by have := hk i;omega
  have hall : ∀j,k.val j=0 := by
    intro j
    apply coordinate_cartan_induction A hd hs hp ho (fun a=>k.val a=0) i j hzero
    intro a b ha hab
    exact dominant_zero_propagates A ho k.val hk hdom a b ha hab
  have hkzero : k.val=0 := by funext j;exact hall j
  have hn := k.property
  rw [hkzero] at hn
  norm_num at hn

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantSupport
