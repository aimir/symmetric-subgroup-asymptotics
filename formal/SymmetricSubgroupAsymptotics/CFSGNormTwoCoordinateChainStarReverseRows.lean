import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarForwardRows
import SymmetricSubgroupAsymptotics.CFSGSignedSwapParameterAction
import Mathlib.Tactic.Group

/-! The actual simple Weyl word realizes a signed swap of the WHOLE
additive root-star. Conjugating the proved forward row by that word,
with the explicit unit rescaling, realizes the reverse row. No arbitrary
negative-root collecting identity or ambient SL lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarReverseRows
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGExceptionalChainStarData CFSGNormTwoCoordinateRootStarHom
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateChainStarRootActions
open CFSGNormTwoCoordinateChainStarForwardRows CFSGNormTwoGeckIntegralRealization
open CFSGAdditiveParameterConjugation CFSGSignedSwapParameterAction CFSGTypeAElementaryMatrices
variable {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] (C : ChainStar A n)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem simple_weyl_action (j : Fin n) :
    ∃d:Fin (n+1)→Kˣ,∀v:Fin (n+1)→K,
      canonicalWeyl D K (C.step j)*
        rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd v)*
        (canonicalWeyl D K (C.step j))⁻¹=
      rawHom A hd hs hp ho K C.root C.pair
        (Multiplicative.ofAdd (signedSwap j.castSucc j.succ d v)) := by
  choose ε hε he using (fun k:Fin (n+1)=>simple_weyl_sign A hd hs hp ho C j k)
  let d (k:Fin (n+1)) : Kˣ := Units.mk0 (ε k:K) (by
    rcases hε k with h|h <;> rw [h] <;> norm_num)
  refine ⟨d,?_⟩
  intro v
  apply conjugation_of_single (rawHom A hd hs hp ho K C.root C.pair)
    (signedSwap j.castSucc j.succ d).toAddEquiv
  intro k a
  change _=rawHom A hd hs hp ho K C.root C.pair
    (Multiplicative.ofAdd (signedSwap j.castSucc j.succ d (Pi.single k a)))
  rw [rawHom_single,signedSwap_single,rawHom_single]
  exact he k K a

theorem reverse_row (j : Fin n) (a : K) :
    ∃t:K,∀v:Fin (n+1)→K,
      (canonicalWeyl D K (C.step j)*canonicalRoot D K false (C.step j) t*
        (canonicalWeyl D K (C.step j))⁻¹)*
        rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd v)*
        (canonicalWeyl D K (C.step j)*canonicalRoot D K false (C.step j) t*
          (canonicalWeyl D K (C.step j))⁻¹)⁻¹=
      rawHom A hd hs hp ho K C.root C.pair
        (Multiplicative.ofAdd ((elementary (by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_succ,Fin.val_castSucc] at hv
          omega : j.castSucc≠j.succ) a).toLin' v)) := by
  let hpq : j.castSucc≠j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ,Fin.val_castSucc] at hv
    omega
  obtain ⟨d,hW⟩ := simple_weyl_action A hd hs hp ho K C j
  let e := signedSwap j.castSucc j.succ d
  let W := canonicalWeyl D K (C.step j)
  let psi := rawHom A hd hs hp ho K C.root C.pair
  have hwinv (v:Fin (n+1)→K) : W⁻¹*psi (Multiplicative.ofAdd v)*W=
      psi (Multiplicative.ofAdd (e.symm v)) := by
    have hh := hW (e.symm v)
    change W*psi (Multiplicative.ofAdd (e.symm v))*W⁻¹=psi (Multiplicative.ofAdd (e (e.symm v))) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    calc
      _=W⁻¹*(W*psi (Multiplicative.ofAdd (e.symm v))*W⁻¹)*W := by rw [hh]
      _=_ := by group
  obtain ⟨t,ht⟩ := forward_row A hd hs hp ho K C j ((d j.castSucc:K)*(d j.succ:K)⁻¹*a)
  refine ⟨t,?_⟩
  intro v
  let g := canonicalRoot D K false (C.step j) t
  change (W*g*W⁻¹)*psi (Multiplicative.ofAdd v)*(W*g*W⁻¹)⁻¹=
    psi (Multiplicative.ofAdd ((elementary hpq a).toLin' v))
  calc
    _=W*(g*(W⁻¹*psi (Multiplicative.ofAdd v)*W)*g⁻¹)*W⁻¹ := by group
    _=W*(g*psi (Multiplicative.ofAdd (e.symm v))*g⁻¹)*W⁻¹ := by rw [hwinv]
    _=W*psi (Multiplicative.ofAdd
        ((elementary hpq.symm ((d j.castSucc:K)*(d j.succ:K)⁻¹*a)).toLin' (e.symm v)))*W⁻¹ := by
      rw [ht]
    _=psi (Multiplicative.ofAdd
        (e ((elementary hpq.symm ((d j.castSucc:K)*(d j.succ:K)⁻¹*a)).toLin' (e.symm v)))) := hW _
    _=_ := congrArg (fun z=>psi (Multiplicative.ofAdd z))
      (conjugate_forward j.castSucc j.succ hpq d a v)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarReverseRows
