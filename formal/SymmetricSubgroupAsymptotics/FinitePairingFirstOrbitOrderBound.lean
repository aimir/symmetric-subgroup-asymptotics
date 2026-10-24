import SymmetricSubgroupAsymptotics.FiniteBilinearIsometryOrderBound

/-! The first basis-vector orbit can be charged by its actual carrier,
rather than by the whole vector space. The remaining basis-prefix
fibres use the same preserved separating pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FinitePairingFirstOrbitOrderBound
open Module FiniteBilinearPrefixOrbits FiniteBilinearIsometryOrderBound

theorem card_le_of_first_orbit {F V G : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Finite V] [Group G] [Finite G]
    {n : ℕ} (b : Basis (Fin (n+1)) F V)
    (rho : G →* (V ≃ₗ[F] V)) (hinj : Function.Injective rho)
    (B : V → V → F)
    (hsep : ∀ x y : V, (∀ i : Fin (n+1), B (b i) x = B (b i) y) → x = y)
    (hpres : ∀ g : G, ∀ x y : V, B (rho g x) (rho g y) = B x y)
    (S : Set V) (hS : ∀ g : G, rho g (b 0) ∈ S) :
    Nat.card G ≤ Nat.card S * Nat.card F ^ (n*(n+1)/2) := by
  have htail (d : ℕ) : ∀ k : ℕ, k+d=n+1 →
      Nat.card (prefixSubgroup rho b k) ≤ Nat.card F ^ triangular d := by
    induction d with
    | zero =>
      intro k hk
      have hk' : k=n+1 := by omega
      subst k
      rw [prefix_end_card rho b hinj]
      rfl
    | succ d ih =>
      intro k hk
      have hk' : k<n+1 := by omega
      have hn : (n+1)-k=d+1 := by omega
      calc
        Nat.card (prefixSubgroup rho b k) ≤
            Nat.card F ^ ((n+1)-k) * Nat.card (prefixSubgroup rho b (k+1)) :=
          next_step_card rho b B hsep hpres k hk'
        _ ≤ Nat.card F ^ ((n+1)-k) * Nat.card F ^ triangular d :=
          Nat.mul_le_mul_left _ (ih (k+1) (by omega))
        _ = Nat.card F ^ triangular (d+1) := by
          rw [hn, ← pow_add]
          rfl
  have ht := htail n 1 (by omega)
  rw [triangular_eq] at ht
  letI : MulAction G V :=
    { smul := fun g v => rho g v
      one_smul := fun v => by change rho 1 v=v; rw [map_one]; rfl
      mul_smul := fun g h v => by
        change rho (g*h) v=rho g (rho h v)
        rw [map_mul]
        rfl }
  let O := MulAction.orbit G (b 0)
  let f : O → S := fun v => ⟨v.val, by
    obtain ⟨g,hg⟩ := v.property
    change rho g (b 0)=v.val at hg
    exact hg ▸ hS g⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun u : S => u.val) he)
  have hO : Nat.card O ≤ Nat.card S := Nat.card_le_card_of_injective f hf
  let T := MulAction.stabilizer G (b 0)
  let e : T ≃ prefixSubgroup rho b 1 :=
    { toFun := fun g => ⟨g.val, by
        intro i hi
        have he : i=0 := Fin.ext (by change i.val=0; omega)
        subst i
        exact g.property⟩
      invFun := fun g => ⟨g.val, g.property 0 (by change (0:ℕ)<1; decide)⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  calc
    Nat.card G = Nat.card O * Nat.card T := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G (b 0))).symm
    _ ≤ Nat.card S * Nat.card (prefixSubgroup rho b 1) := by
      rw [Nat.card_congr e]
      exact Nat.mul_le_mul_right _ hO
    _ ≤ _ := Nat.mul_le_mul_left _ ht

end SymmetricSubgroupAsymptotics.FinitePairingFirstOrbitOrderBound
