import SymmetricSubgroupAsymptotics.PrimeSocleElementaryChart

/-! A quotient of an actual subgroup of c binary coordinates has an actual
binary chart of rank at most c. Neither a complement nor a count is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCoordinateSurjectiveQuotient
open scoped IsMulCommutative
variable {Z A : Type} [Group Z] [Group A] [Finite Z] [Finite A] {c : ℕ}

private theorem binary_square (v : Multiplicative (ZMod 2)) : v^2=1 := by
  revert v
  decide +kernel

theorem exists_chart (e : Z →* (Fin c → Multiplicative (ZMod 2)))
    (he : Function.Injective e) (q : Z →* A) (hq : Function.Surjective q) :
    ∃ r : ℕ, r≤c ∧ Nonempty (A ≃* (Fin r → Multiplicative (ZMod 2))) := by
  letI : IsMulCommutative Z := IsMulCommutative.of_comm (fun x y => he (by
    rw [map_mul,map_mul,mul_comm]))
  letI : IsMulCommutative A := IsMulCommutative.of_comm (by
    intro x y
    obtain ⟨a,rfl⟩ := hq x
    obtain ⟨b,rfl⟩ := hq y
    rw [← map_mul,← map_mul,mul_comm])
  have hz2 (z : Z) : z^2=1 := he (by
    rw [map_pow,map_one]
    funext i
    exact binary_square (e z i))
  have ha2 (a : A) : a^2=1 := by
    obtain ⟨z,rfl⟩ := hq a
    rw [← map_pow,hz2,map_one]
  letI : Module (ZMod 2) (Additive Z) := AddCommGroup.zmodModule (n := 2)
    (fun z => by apply Additive.toMul.injective; exact hz2 z.toMul)
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2)
    (fun a => by apply Additive.toMul.injective; exact ha2 a.toMul)
  let el : Additive Z →ₗ[ZMod 2] (Fin c → ZMod 2) :=
    (show Additive Z →+ (Fin c → ZMod 2) from
      { toFun := fun z i => (e z.toMul i).toAdd
        map_zero' := by funext i; exact congrArg (fun v => (v i).toAdd) e.map_one
        map_add' := by
          intro x y
          funext i
          exact congrArg (fun v => (v i).toAdd) (e.map_mul x.toMul y.toMul) }).toZModLinearMap 2
  have hel : Function.Injective el := by
    intro x y h
    apply Additive.toMul.injective
    apply he
    funext i
    exact Multiplicative.toAdd.injective (congrFun h i)
  let ql : Additive Z →ₗ[ZMod 2] Additive A := q.toAdditive.toZModLinearMap 2
  have hql : Function.Surjective ql := by
    intro a
    obtain ⟨z,hz⟩ := hq a.toMul
    exact ⟨Additive.ofMul z,congrArg Additive.ofMul hz⟩
  have hr : Module.finrank (ZMod 2) (Additive A)≤c := by
    have h1 := LinearMap.finrank_le_finrank_of_surjective (f := ql) hql
    have h2 := LinearMap.finrank_le_finrank_of_injective (f := el) hel
    exact h1.trans (by simpa only [Module.finrank_pi,Fintype.card_fin] using h2)
  let b := (Module.finBasis (ZMod 2) (Additive A)).equivFun
  refine ⟨Module.finrank (ZMod 2) (Additive A),hr,⟨?_⟩⟩
  exact
    { toFun := fun a i => Multiplicative.ofAdd (b (Additive.ofMul a) i)
      invFun := fun v => (b.symm (fun i => (v i).toAdd)).toMul
      left_inv := by intro a; exact congrArg Additive.toMul (b.symm_apply_apply _)
      right_inv := by
        intro v
        funext i
        apply Multiplicative.toAdd.injective
        exact congrFun (b.apply_symm_apply (fun j => (v j).toAdd)) i
      map_mul' := by
        intro a a'
        funext i
        exact congrArg (fun v => Multiplicative.ofAdd (v i)) (b.map_add (Additive.ofMul a) (Additive.ofMul a')) }

end SymmetricSubgroupAsymptotics.BinaryCoordinateSurjectiveQuotient
