import SymmetricSubgroupAsymptotics.FiniteHermitianBasisCoordinates
import SymmetricSubgroupAsymptotics.FiniteDiagonalNormShellRecurrence
import SymmetricSubgroupAsymptotics.FiniteBilinearPrefixOrbits

/-! The next orbit of an orthonormal-basis prefix stabilizer injects
into the actual norm-one shell in its remaining coordinates. The SAME
source subgroup and its actual point stabilizer are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteHermitianPrefixOrbits
open Module FiniteHermitianBasisCoordinates FiniteBilinearPrefixOrbits

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]
    [Finite K] [Finite G]
variable (rho : G →* (V ≃ₗ[K] V)) {n : ℕ} (b : Basis (Fin n) K V) (sigma : K ≃+* K)

private abbrev linearAction {A : Type*} [Group A]
    (r : A →* (V ≃ₗ[K] V)) : MulAction A V where
  smul g v := r g v
  one_smul v := by
    change r 1 v=v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change r (g*h) v=r g (r h v)
    rw [map_mul]
    rfl

theorem next_step_card
    (hpres : ∀ g : G, ∀ x y : V,
      coordinatePair sigma b (rho g x) (rho g y)=coordinatePair sigma b x y)
    (k : ℕ) (hk : k < n) :
    Nat.card (prefixSubgroup rho b k) ≤
      FiniteDiagonalNormShellRecurrence.shellCard (fun a : K => sigma a*a) (n-k)*
        Nat.card (prefixSubgroup rho b (k+1)) := by
  classical
  let P := prefixSubgroup rho b k
  let r : P →* (V ≃ₗ[K] V) := rho.comp P.subtype
  letI : MulAction P V := linearAction r
  let v := b ⟨k,hk⟩
  let O := MulAction.orbit P v
  have hearlier (y : O) (i : Fin n) (hi : i.val < k) : b.repr y.val i=0 := by
    obtain ⟨g,hg⟩ := y.property
    change r g v=y.val at hg
    have hfix : rho g.val (b i)=b i := g.property i hi
    have hine : i ≠ (⟨k,hk⟩ : Fin n) := by
      intro he
      have hh := congrArg Fin.val he
      change i.val=k at hh
      omega
    rw [←coordinatePair_basis_left sigma b i y.val,←hg]
    change coordinatePair sigma b (b i) (rho g.val v)=0
    calc
      _ = coordinatePair sigma b (rho g.val (b i)) (rho g.val v) :=
        congrArg (fun x => coordinatePair sigma b x (rho g.val v)) hfix.symm
      _ = coordinatePair sigma b (b i) v := hpres g.val (b i) v
      _ = 0 := by simp [coordinatePair_basis_left,v,hine]
  have hnorm (y : O) : coordinatePair sigma b y.val y.val=1 := by
    obtain ⟨g,hg⟩ := y.property
    change r g v=y.val at hg
    rw [←hg]
    change coordinatePair sigma b (rho g.val v) (rho g.val v)=1
    rw [hpres]
    simp [coordinatePair_basis_left,v]
  let encode : O → {z : Fin (n-k) → K // ∑ j, sigma (z j)*z j=1} := fun y =>
    ⟨fun j => b.repr y.val ⟨k+j.val,by omega⟩,
      (norm_tail_of_prefix_zero sigma b y.val k hk.le (hearlier y)).symm.trans (hnorm y)⟩
  have hinj : Function.Injective encode := by
    intro y z he
    apply Subtype.ext
    apply b.repr.injective
    apply Finsupp.ext
    intro i
    by_cases hi : i.val < k
    · exact (hearlier y i hi).trans (hearlier z i hi).symm
    · have hj := congrFun (congrArg Subtype.val he) (⟨i.val-k,by omega⟩ : Fin (n-k))
      change b.repr y.val ⟨k+(i.val-k),by omega⟩=
        b.repr z.val ⟨k+(i.val-k),by omega⟩ at hj
      have heq : (⟨k+(i.val-k),by omega⟩ : Fin n)=i := by
        apply Fin.ext
        change k+(i.val-k)=i.val
        omega
      simpa only [heq] using hj
  have hO : Nat.card O ≤
      FiniteDiagonalNormShellRecurrence.shellCard (fun a : K => sigma a*a) (n-k) :=
    Nat.card_le_card_of_injective encode hinj
  letI : Finite O := Finite.of_injective encode hinj
  let S := MulAction.stabilizer P v
  let e : S ≃ prefixSubgroup rho b (k+1) :=
    { toFun := fun g => ⟨g.val.val,by
        intro i hi
        by_cases hik : i.val < k
        · exact g.val.property i hik
        · have heq : i=(⟨k,hk⟩ : Fin n) := Fin.ext (by change i.val=k; omega)
          subst i
          exact g.property⟩
      invFun := fun g => ⟨⟨g.val,fun i hi => g.property i (by omega)⟩,
        g.property ⟨k,hk⟩ (by change k<k+1; omega)⟩
      left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun g => by apply Subtype.ext; rfl }
  calc
    Nat.card P=Nat.card O*Nat.card S := by
      rw [←Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup P v)).symm
    _ ≤ FiniteDiagonalNormShellRecurrence.shellCard (fun a : K => sigma a*a) (n-k)*
        Nat.card S := Nat.mul_le_mul_right _ hO
    _ = _ := by rw [Nat.card_congr e]

end SymmetricSubgroupAsymptotics.FiniteHermitianPrefixOrbits
