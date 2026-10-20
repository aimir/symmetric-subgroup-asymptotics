import SymmetricSubgroupAsymptotics.MarkedC4ActiveFiberPermutation
import SymmetricSubgroupAsymptotics.MarkedC4CoprimeGridEquivariance

/-! Coprime direct factors admit faithful actions on disjoint compressed
supports whose total size is at most the original faithful degree. Every
coordinate comes from an original orbit stabilizer. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.CoprimeFaithfulSupportCompression
open MarkedC4

variable (A B X : Type) [Group A] [Group B] [Finite A] [Finite B]
  [MulAction (A × B) X]

abbrev OrbitIndex := MulAction.orbitRel.Quotient (A × B) X
abbrev LeftFiber (o : OrbitIndex A B X) :=
  A ⧸ ((MulAction.stabilizer (A × B) o.out).map (MonoidHom.fst A B))
abbrev RightFiber (o : OrbitIndex A B X) :=
  B ⧸ ((MulAction.stabilizer (A × B) o.out).map (MonoidHom.snd A B))
abbrev LeftSupport := ActiveFiberPermutation.Support (LeftFiber A B X)
abbrev RightSupport := ActiveFiberPermutation.Support (RightFiber A B X)

def pointGrid (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    X ≃ Σ o : OrbitIndex A B X, LeftFiber A B X o × RightFiber A B X o :=
  (MulAction.selfEquivSigmaOrbits (A × B) X).trans
    (Equiv.sigmaCongrRight fun o => CoprimePhysicalGrid.orbitGrid hcop o.out)

variable (hcop : Nat.Coprime (Nat.card A) (Nat.card B))

include hcop in
theorem fixes_original (a : A) (b : B)
    (ha : ∀ o (x : LeftFiber A B X o), a • x = x)
    (hb : ∀ o (x : RightFiber A B X o), b • x = x) :
    ∀ x : X, (a, b) • x = x := by
  intro x
  let z := MulAction.selfEquivSigmaOrbits (A × B) X x
  have hzval : (z.2 : X) = x := rfl
  have hgrid : CoprimePhysicalGrid.orbitGrid hcop z.1.out ((a, b) • z.2) =
      CoprimePhysicalGrid.orbitGrid hcop z.1.out z.2 := by
    rw [CoprimeGridEquivariance.grid_equivariant]
    exact Prod.ext (ha z.1 _) (hb z.1 _)
  have hz := (CoprimePhysicalGrid.orbitGrid hcop z.1.out).injective hgrid
  simpa only [hzval] using congrArg Subtype.val hz

variable [FaithfulSMul (A × B) X]

include hcop in
theorem faithful_left : FaithfulSMul A (LeftSupport A B X) where
  eq_of_smul_eq_smul := by
    intro a b hab
    have hfix : ∀ z : LeftSupport A B X, (a⁻¹ * b) • z = z := by
      intro z
      rw [mul_smul, ← hab z, inv_smul_smul]
    have hleft := (ActiveFiberPermutation.fixes_iff (LeftFiber A B X) (a⁻¹ * b)).mp hfix
    have hpair : (a⁻¹ * b, (1 : B)) = (1 : A × B) :=
      eq_of_smul_eq_smul (α := X) (fun x => by
        rw [one_smul]
        exact fixes_original A B X hcop (a⁻¹ * b) 1 hleft (fun _ _ => one_smul _ _) x)
    exact inv_mul_eq_one.mp (congrArg Prod.fst hpair)

include hcop in
theorem faithful_right : FaithfulSMul B (RightSupport A B X) where
  eq_of_smul_eq_smul := by
    intro a b hab
    have hfix : ∀ z : RightSupport A B X, (a⁻¹ * b) • z = z := by
      intro z
      rw [mul_smul, ← hab z, inv_smul_smul]
    have hright := (ActiveFiberPermutation.fixes_iff (RightFiber A B X) (a⁻¹ * b)).mp hfix
    have hpair : ((1 : A), a⁻¹ * b) = (1 : A × B) :=
      eq_of_smul_eq_smul (α := X) (fun x => by
        rw [one_smul]
        exact fixes_original A B X hcop 1 (a⁻¹ * b) (fun _ _ => one_smul _ _) hright x)
    exact inv_mul_eq_one.mp (congrArg Prod.snd hpair)

omit [FaithfulSMul (A × B) X] in
include hcop in
theorem support_budget [Finite X] :
    Nat.card (LeftSupport A B X) + Nat.card (RightSupport A B X) ≤ Nat.card X := by
  letI : Fintype (OrbitIndex A B X) := Fintype.ofFinite _
  rw [ActiveFiberPermutation.card_support, ActiveFiberPermutation.card_support,
    Nat.card_congr (pointGrid A B X hcop), Nat.card_sigma]
  simp_rw [Nat.card_prod]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ =>
    CoprimePhysicalGrid.activeDegree_budget Nat.card_pos Nat.card_pos)

end SymmetricSubgroupAsymptotics.CoprimeFaithfulSupportCompression
