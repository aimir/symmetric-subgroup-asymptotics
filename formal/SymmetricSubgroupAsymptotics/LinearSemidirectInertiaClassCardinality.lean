import SymmetricSubgroupAsymptotics.LinearSemidirectCommutingFibres

/-! The class number of an actual linear semidirect product equals
the number of inertia orbits on its actual contragredient dual.
The equality retains every commuting complement pair. It uses only
linear rank/nullity and the finite action counting identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.LinearSemidirectInertiaClassCardinality
open LinearSemidirectCommutingFibres AbelianActionClassBound
open InvariantAnnihilatorOrbitIndex AffineInertiaOrbitDomination GroupActionInertia

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

def commutingJointFixedEquiv (ρ : G →* (V ≃ₗ[K] V)) :
    letI := dualAction ρ
    (Σ t : CommutingPairs G, jointFixed (Module.Dual K V) t.val.1 t.val.2) ≃
      Σ h : G, MulAction.fixedBy (inertia G (Module.Dual K V)) h := by
  letI := dualAction ρ
  exact {
    toFun p := ⟨p.1.val.2, (fixedInertiaEquiv p.1.val.2).symm
      ⟨⟨p.1.val.1, p.1.property⟩, p.2⟩⟩
    invFun p := by
      let q := fixedInertiaEquiv p.1 p.2
      exact ⟨⟨(q.1.val, p.1), q.1.property⟩, q.2⟩
    left_inv p := by
      rcases p with ⟨⟨⟨g, h⟩, hc⟩, x⟩
      exact congrArg
        (fun q : Σ a : {a : G // a*h=h*a},
            jointFixed (Module.Dual K V) a.val h =>
          (⟨⟨(q.1.val,h),q.1.property⟩,q.2⟩ :
            Σ t : CommutingPairs G, jointFixed (Module.Dual K V) t.val.1 t.val.2))
        ((fixedInertiaEquiv h).apply_symm_apply ⟨⟨g,hc⟩,x⟩)
    right_inv p := by
      rcases p with ⟨h, x⟩
      apply Sigma.ext rfl
      apply heq_of_eq
      change (fixedInertiaEquiv h).symm ((fixedInertiaEquiv h) x) = x
      exact (fixedInertiaEquiv h).symm_apply_apply x }

theorem commuting_card [Finite G] [Finite K] [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) :
    letI := dualAction ρ
    Nat.card (CommutingPairs (AffineGroup ρ)) =
      Nat.card V *
        (Nat.card (MulAction.orbitRel.Quotient G (inertia G (Module.Dual K V))) *
          Nat.card G) := by
  letI := dualAction ρ
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (Module.Dual K V) := Module.finite_of_finite K
  letI : Finite (Multiplicative V) := Finite.of_equiv V Multiplicative.ofAdd
  letI : Fintype (CommutingPairs G) := Fintype.ofFinite _
  calc
    _ = ∑ t : CommutingPairs G,
        Nat.card (AbelianActionCommutingFibreBound.Fibre (linearActionHom ρ)
          t.val.1 t.val.2) := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (commutingEquiv (linearActionHom ρ))
    _ = ∑ t : CommutingPairs G,
        Nat.card V * Nat.card (jointFixed (Module.Dual K V) t.val.1 t.val.2) := by
      apply Finset.sum_congr rfl
      intro t _
      exact commuting_fibre_card ρ t.val.1 t.val.2 t.property
    _ = Nat.card V *
        Nat.card (Σ t : CommutingPairs G,
          jointFixed (Module.Dual K V) t.val.1 t.val.2) := by
      rw [Nat.card_sigma, Finset.mul_sum]
    _ = Nat.card V * Nat.card
        (Σ h : G, MulAction.fixedBy (inertia G (Module.Dual K V)) h) :=
      congrArg (fun n : ℕ => Nat.card V * n)
        (Nat.card_congr (commutingJointFixedEquiv ρ))
    _ = _ := by
      rw [Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup G
        (inertia G (Module.Dual K V))), Nat.card_prod]

theorem class_card_eq_dual_inertia [Finite G] [Finite K] [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) :
    letI := dualAction ρ
    Nat.card (ConjClasses (AffineGroup ρ)) =
      Nat.card (MulAction.orbitRel.Quotient G (inertia G (Module.Dual K V))) := by
  letI := dualAction ρ
  letI : Finite V := Module.finite_of_finite K
  have hc := commuting_card ρ
  rw [card_comm_eq_card_conjClasses_mul_card, SemidirectProduct.card] at hc
  change Nat.card (ConjClasses (AffineGroup ρ)) * (Nat.card V * Nat.card G) =
    Nat.card V *
      (Nat.card (MulAction.orbitRel.Quotient G (inertia G (Module.Dual K V))) *
        Nat.card G) at hc
  have he : Nat.card (ConjClasses (AffineGroup ρ)) * (Nat.card V * Nat.card G) =
      Nat.card (MulAction.orbitRel.Quotient G (inertia G (Module.Dual K V))) *
        (Nat.card V * Nat.card G) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hc
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.card_pos (α := V))
    (Nat.card_pos (α := G))) he

end SymmetricSubgroupAsymptotics.LinearSemidirectInertiaClassCardinality
