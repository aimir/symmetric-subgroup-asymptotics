import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.GroupTheory.GroupAction.Quotient
import Lean.Elab.Tactic.Omega

/-! Prefix stabilizers of a literal bilinear isometry action. The orbit
of the next basis vector is encoded by the remaining pairings; the
earlier pairings are fixed by the actual preserved form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBilinearPrefixOrbits
open Module
variable {F V G : Type*} [Field F] [AddCommGroup V] [Module F V] [Group G]
variable (rho : G →* (V ≃ₗ[F] V)) {n : ℕ} (b : Basis (Fin n) F V)

def prefixSubgroup (k : ℕ) : Subgroup G where
  carrier := {g | ∀ i : Fin n, i.val < k → rho g (b i) = b i}
  one_mem' := by
    intro i hi
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh i hi
    rw [map_mul, LinearEquiv.mul_apply, hh i hi, hg i hi]
  inv_mem' := by
    intro g hg i hi
    apply (rho g).injective
    rw [map_inv]
    change rho g ((rho g).symm (b i)) = rho g (b i)
    rw [LinearEquiv.apply_symm_apply, hg i hi]

theorem mem_prefix (k : ℕ) (g : G) :
    g ∈ prefixSubgroup rho b k ↔ ∀ i : Fin n, i.val < k → rho g (b i) = b i := Iff.rfl

private abbrev linearAction {A : Type*} [Group A]
    (r : A →* (V ≃ₗ[F] V)) : MulAction A V where
  smul g v := r g v
  one_smul v := by
    change r 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change r (g * h) v = r g (r h v)
    rw [map_mul]
    rfl

theorem next_step_card [Finite F] [Finite G]
    (B : V → V → F)
    (hsep : ∀ x y : V, (∀ i : Fin n, B (b i) x = B (b i) y) → x = y)
    (hpres : ∀ g : G, ∀ x y : V, B (rho g x) (rho g y) = B x y)
    (k : ℕ) (hk : k < n) :
    Nat.card (prefixSubgroup rho b k) ≤
      Nat.card F ^ (n - k) * Nat.card (prefixSubgroup rho b (k + 1)) := by
  classical
  let P := prefixSubgroup rho b k
  let r : P →* (V ≃ₗ[F] V) := rho.comp P.subtype
  letI : MulAction P V := linearAction r
  let v := b ⟨k, hk⟩
  let O := MulAction.orbit P v
  let encode : O → (Fin (n-k) → F) := fun y j =>
    B (b ⟨k+j.val, by omega⟩) y.val
  have hearlier (y : O) (i : Fin n) (hi : i.val < k) :
      B (b i) y.val = B (b i) v := by
    obtain ⟨g, hg⟩ := y.property
    change r g v = y.val at hg
    rw [← hg]
    have hfix : rho g.val (b i) = b i := g.property i hi
    change B (b i) (rho g.val v) = B (b i) v
    calc
      B (b i) (rho g.val v) = B (rho g.val (b i)) (rho g.val v) :=
        congrArg (fun x => B x (rho g.val v)) hfix.symm
      _ = B (b i) v := hpres g.val (b i) v
  have hinj : Function.Injective encode := by
    intro y z he
    apply Subtype.ext
    apply hsep
    intro i
    by_cases hi : i.val < k
    · exact (hearlier y i hi).trans (hearlier z i hi).symm
    · have hj := congrFun he (⟨i.val-k, by omega⟩ : Fin (n-k))
      change B (b ⟨k+(i.val-k), by omega⟩) y.val =
        B (b ⟨k+(i.val-k), by omega⟩) z.val at hj
      have heq : (⟨k+(i.val-k), by omega⟩ : Fin n) = i := by
        apply Fin.ext
        change k+(i.val-k)=i.val
        omega
      simpa only [heq] using hj
  have hO : Nat.card O ≤ Nat.card F ^ (n-k) := by
    have h := Nat.card_le_card_of_injective encode hinj
    simpa only [Nat.card_fun, Nat.card_fin] using h
  letI : Finite O := Finite.of_injective encode hinj
  let S := MulAction.stabilizer P v
  let e : S ≃ prefixSubgroup rho b (k+1) :=
    { toFun := fun g => ⟨g.val.val, by
        intro i hi
        by_cases hik : i.val < k
        · exact g.val.property i hik
        · have heq : i = (⟨k, hk⟩ : Fin n) := Fin.ext (by change i.val=k; omega)
          subst i
          exact g.property⟩
      invFun := fun g => ⟨⟨g.val, fun i hi => g.property i (by omega)⟩,
        g.property ⟨k, hk⟩ (by change k<k+1; omega)⟩
      left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun g => by apply Subtype.ext; rfl }
  calc
    Nat.card P = Nat.card O * Nat.card S := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup P v)).symm
    _ ≤ Nat.card F ^ (n-k) * Nat.card S := Nat.mul_le_mul_right _ hO
    _ = Nat.card F ^ (n-k) * Nat.card (prefixSubgroup rho b (k+1)) := by
      rw [Nat.card_congr e]

theorem prefix_zero_card : Nat.card (prefixSubgroup rho b 0) = Nat.card G := by
  let e : prefixSubgroup rho b 0 ≃ G :=
    { toFun := Subtype.val
      invFun := fun g => ⟨g, fun i hi => by omega⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  exact Nat.card_congr e

theorem prefix_end_card (hinj : Function.Injective rho) :
    Nat.card (prefixSubgroup rho b n) = 1 := by
  have hfix (g : prefixSubgroup rho b n) : g = 1 := by
    apply Subtype.ext
    apply hinj
    apply b.ext'
    intro i
    change rho g.val (b i) = rho 1 (b i)
    rw [map_one]
    exact g.property i i.isLt
  letI : Unique (prefixSubgroup rho b n) :=
    { default := 1
      uniq := hfix }
  exact Nat.card_unique

end SymmetricSubgroupAsymptotics.FiniteBilinearPrefixOrbits
