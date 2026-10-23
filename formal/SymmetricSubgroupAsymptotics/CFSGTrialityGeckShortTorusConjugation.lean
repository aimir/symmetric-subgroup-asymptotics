import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortParameterWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation
import Mathlib.Tactic.Group

/-! The literal fixed short-orbit torus scales its whole extension-field
root parameter by a squared unit.  This is a proved natural matrix-word
identity, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortTorusConjugation
open CFSGTrialityGeckShortParameterWeyl CFSGTrialityD4NormTwo
open CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGTrialityGeckFixedRootWords CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckTorusConjugation CFSGIntegerMatrixPairing

private abbrev outerWeyl (K : Type) [Field K] (i : Fin 3) (a : Kˣ) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  parameterWeyl (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    Base Index K (outerNode i) a

private abbrev outerTorus (K : Type) [Field K] (i : Fin 3) (a : Kˣ) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    Base Index K (outerNode i) a

private theorem outer_weyl_root_commute (K : Type) [Field K]
    (i j : Fin 3) (hij : i ≠ j) (a : Kˣ) (e : Bool) (t : K) :
    Commute (outerWeyl K i a) (canonicalRoot rawData K e (outerNode j) t) :=
  ((CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K i j hij false e (a : K) t).mul_left
    (CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K i j hij true e (-(a : K)⁻¹) t)).mul_left
    (CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K i j hij false e (a : K) t)

private theorem outer_weyls_commute (K : Type) [Field K]
    (i j : Fin 3) (hij : i ≠ j) (a b : Kˣ) :
    Commute (outerWeyl K i a) (outerWeyl K j b) :=
  ((outer_weyl_root_commute K i j hij a false (b : K)).mul_right
    (outer_weyl_root_commute K i j hij a true (-(b : K)⁻¹))).mul_right
    (outer_weyl_root_commute K i j hij a false (b : K))

def shortTorusWord (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :=
  shortWeylWord K σ a * (shortWeylWord K σ 1)⁻¹

theorem shortTorusWord_eq_product (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :
    shortTorusWord K σ a =
      outerTorus K 0 a * outerTorus K 1 (unitFieldMap K σ a) *
        outerTorus K 2 (unitFieldMap K σ (unitFieldMap K σ a)) := by
  let T (i : Fin 3) := outerTorus K i (outerParameters K σ a i)
  let R (i : Fin 3) := outerWeyl K i 1
  have hcomm (i j : Fin 3) (hij : i ≠ j) : Commute (T i) (R j) :=
    (outer_weyls_commute K i j hij (outerParameters K σ a i) 1).mul_left
      (outer_weyls_commute K i j hij 1 1).inv_left
  have hp : (T 0*T 1*T 2)*(R 0*R 1*R 2) =
      (T 0*R 0)*(T 1*R 1)*(T 2*R 2) := by
    calc
      _ = (T 0*T 1)*(R 0*R 1)*(T 2*R 2) :=
        ((hcomm 2 0 (by decide)).mul_right (hcomm 2 1 (by decide))).mul_mul_mul_comm _ _
      _ = _ := congrArg (fun x => x*(T 2*R 2))
        ((hcomm 1 0 (by decide)).mul_mul_mul_comm (T 0) (R 1))
  have hnode (i : Fin 3) : T i*R i = outerWeyl K i (outerParameters K σ a i) := by
    dsimp only [T,R,outerTorus,parameterTorus,outerWeyl]
    group
  have hW1 : shortWeylWord K σ 1 = R 0*R 1*R 2 := by
    rw [shortWeylWord_eq_product]
    simp only [map_one]
    rfl
  have hTW : (T 0*T 1*T 2)*shortWeylWord K σ 1 = shortWeylWord K σ a := by
    rw [hW1,hp,hnode 0,hnode 1,hnode 2]
    symm
    exact shortWeylWord_eq_product K σ a
  have he : T 0*T 1*T 2 = shortTorusWord K σ a := by
    calc
      _ = ((T 0*T 1*T 2)*shortWeylWord K σ 1)*(shortWeylWord K σ 1)⁻¹ := by group
      _ = shortTorusWord K σ a := by rw [hTW];rfl
  exact he.symm

private theorem outer_pairing (i j : Fin 3) :
    integerPairing (CartanMatrix.D 4) (Index (outerNode i) :
      CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val
      (Index (outerNode j) : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val =
        if i = j then 2 else 0 := by
  change integerPairing (CartanMatrix.D 4)
    (Pi.single (outerNode i) (1 : ℤ) : Fin 4 → ℤ)
    (Pi.single (outerNode j) (1 : ℤ) : Fin 4 → ℤ) = _
  fin_cases i <;> fin_cases j <;> decide

private theorem outer_torus_root (K : Type) [Field K] (i j : Fin 3) (a : Kˣ) (t : K) :
    outerTorus K i a * canonicalRoot rawData K false (outerNode j) t *
      (outerTorus K i a)⁻¹ =
        canonicalRoot rawData K false (outerNode j) (if i = j then t*(a : K)^2 else t) := by
  have he := torus_conjugate_positive (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K (outerNode i) (outerNode j) a t
  rw [outer_pairing] at he
  by_cases hij : i = j
  · simpa only [if_pos hij,zpow_ofNat] using he
  · simpa only [if_neg hij,zpow_zero,mul_one] using he

private theorem product_torus_root (K : Type) [Field K] (σ : K ≃+* K)
    (a : Kˣ) (k : Fin 3) (t : K) :
    shortTorusWord K σ a * canonicalRoot rawData K false (outerNode k) t *
      (shortTorusWord K σ a)⁻¹ =
        canonicalRoot rawData K false (outerNode k) (t*(outerParameters K σ a k : K)^2) := by
  rw [shortTorusWord_eq_product]
  let T0 := outerTorus K 0 a
  let T1 := outerTorus K 1 (unitFieldMap K σ a)
  let T2 := outerTorus K 2 (unitFieldMap K σ (unitFieldMap K σ a))
  change (T0*T1*T2)*canonicalRoot rawData K false (outerNode k) t*(T0*T1*T2)⁻¹ = _
  calc
    _ = T0*(T1*(T2*canonicalRoot rawData K false (outerNode k) t*T2⁻¹)*T1⁻¹)*T0⁻¹ := by group
    _ = _ := by
      dsimp only [T0,T1,T2]
      rw [outer_torus_root,outer_torus_root,outer_torus_root]
      fin_cases k <;> simp [outerParameters]

theorem shortTorusWord_conjugate (K : Type) [Field K] (σ : K ≃+* K)
    (a : Kˣ) (t : K) :
    shortTorusWord K σ a * shortOrbit K σ false t * (shortTorusWord K σ a)⁻¹ =
      shortOrbit K σ false (t*(a : K)^2) := by
  let T := shortTorusWord K σ a
  calc
    _ = (T*canonicalRoot rawData K false 0 t*T⁻¹) *
        (T*canonicalRoot rawData K false 2 (σ t)*T⁻¹) *
        (T*canonicalRoot rawData K false 3 (σ (σ t))*T⁻¹) := by
      dsimp only [shortOrbit,T]
      group
    _ = _ := by
      change (T*canonicalRoot rawData K false (outerNode 0) t*T⁻¹) *
        (T*canonicalRoot rawData K false (outerNode 1) (σ t)*T⁻¹) *
        (T*canonicalRoot rawData K false (outerNode 2) (σ (σ t))*T⁻¹) = _
      dsimp only [T]
      rw [product_torus_root,product_torus_root,product_torus_root]
      change canonicalRoot rawData K false 0 (t*(a : K)^2) *
        canonicalRoot rawData K false 2 (σ t*(unitFieldMap K σ a : K)^2) *
        canonicalRoot rawData K false 3
          (σ (σ t)*(unitFieldMap K σ (unitFieldMap K σ a) : K)^2) =
        shortOrbit K σ false (t*(a : K)^2)
      simp only [unitFieldMap_val,shortOrbit,map_mul,map_pow]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortTorusConjugation
