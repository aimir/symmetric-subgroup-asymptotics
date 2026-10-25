import SymmetricSubgroupAsymptotics.SubnormalRealCoordinateClassBound

/-! Power budgets pass through the actual correlated coordinate-kernel
filtration. Each successive factor is a subnormal subgroup of its
original coordinate group. No coordinate independence or class-number
monotonicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SubnormalCoordinateClassPowerBound
open SubnormalCoordinateClassBound

private theorem normal_power_bound
    {H : Type*} [Group H] [Finite H] (d n : ℕ)
    (V : Fin n → Type*) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : Fin n → ℕ) (f : ∀ i, H →* V i)
    (hc : ∀ i (N : Subgroup H), N.Normal →
      Nat.card (ConjClasses (N.map (f i))) ^ d ≤ c i)
    (L : Subgroup H) (hL : L.Normal)
    (hinj : Function.Injective (fun x : L => fun i => f i x.val)) :
    Nat.card (ConjClasses L) ^ d ≤ ∏ i, c i := by
  induction n generalizing L with
  | zero =>
    letI : Subsingleton L := ⟨fun x y => hinj (funext (fun i => Fin.elim0 i))⟩
    have hh := Nat.card_le_card_of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective
    have h1 : Nat.card (ConjClasses L) ≤ 1 := by simpa only [Nat.card_unique] using hh
    simpa only [one_pow,Fin.prod_univ_zero] using Nat.pow_le_pow_left h1 d
  | succ n ih =>
    letI : L.Normal := hL
    let K : Subgroup H := L ⊓ (f 0).ker
    letI : K.Normal := by dsimp only [K]; infer_instance
    have htail : Function.Injective (fun x : K => fun i : Fin n => f i.succ x.val) := by
      intro x y he
      have hxy : (⟨x.val,x.property.1⟩ : L) = ⟨y.val,y.property.1⟩ := by
        apply hinj
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact x.property.2.trans y.property.2.symm
        · exact congrFun he j
      exact Subtype.ext (congrArg (fun z : L => z.val) hxy)
    have hK := ih (fun i : Fin n => V i.succ) (fun i => c i.succ)
      (fun i => f i.succ) (fun i N hN => hc i.succ N hN) K inferInstance htail
    let fL : L →* V 0 := (f 0).comp L.subtype
    let e : fL.ker ≃* K :=
      { toFun := fun x => ⟨x.val.val,⟨x.val.property,x.property⟩⟩
        invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have hker : Nat.card (ConjClasses fL.ker) ≤ Nat.card (ConjClasses K) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    have hrange : fL.range = L.map (f 0) := by
      dsimp only [fL]
      rw [MonoidHom.range_comp,Subgroup.range_subtype]
    have hsplit := Nat.pow_le_pow_left (conjugacyClass_card_le_kernel_mul_range fL) d
    rw [mul_pow,hrange] at hsplit
    rw [Fin.prod_univ_succ]
    exact hsplit.trans ((Nat.mul_le_mul
      ((Nat.pow_le_pow_left hker d).trans hK) (hc 0 L hL)).trans_eq (Nat.mul_comm _ _))

theorem class_power_le_subnormal_coordinate_bounds
    {H : Type*} [Group H] [Finite H] (d n : ℕ)
    (V : Fin n → Type*) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : Fin n → ℕ) (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hc : ∀ i (L : Subgroup (V i)), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ d ≤ c i)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    Nat.card (ConjClasses H) ^ d ≤ ∏ i, c i := by
  have ht := normal_power_bound d n V c f
    (fun i N hN => hc i (N.map (f i))
      (map_normal_isSubnormal_of_range (f i) (himage i) N hN))
    ⊤ Subgroup.normal_top (fun x y he => Subtype.ext (hinj he))
  have he : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses (⊤ : Subgroup H)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom)
      (ConjClasses.map_surjective (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).surjective)
  exact (Nat.pow_le_pow_left he d).trans ht

theorem class_power_le_finite_subnormal_coordinate_bounds
    {ι : Type*} [Fintype ι] (d : ℕ)
    (V : ι → Type*) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : ι → ℕ) (H : Type*) [Group H] [Finite H] (f : ∀ i, H →* V i)
    (himage : ∀ i, (f i).range.IsSubnormal)
    (hc : ∀ i (L : Subgroup (V i)), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ d ≤ c i)
    (hinj : Function.Injective (fun x => fun i => f i x)) :
    Nat.card (ConjClasses H) ^ d ≤ ∏ i, c i := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun x => fun j => f (e j) x) := by
    intro x y he
    apply hinj
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun he j
  have hh := class_power_le_subnormal_coordinate_bounds d (Fintype.card ι)
    (fun j => V (e j)) (fun j => c (e j)) (fun j => f (e j))
    (fun j => himage (e j)) (fun j => hc (e j)) hi
  simpa only [e.prod_comp] using hh

end SymmetricSubgroupAsymptotics.SubnormalCoordinateClassPowerBound
