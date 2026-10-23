import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.GroupTheory.IsSubnormal

/-! Coordinate class budgets need only subnormal component groups when
the actual coordinate images are subnormal. The proof retains every
successive coordinate kernel as a NORMAL subgroup of the ORIGINAL
source. It never treats arbitrary subgroups of the ambient coordinates
as subnormal, and never assumes independent coordinate factors. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SubnormalCoordinateClassBound

theorem map_normal_isSubnormal_of_range {H V : Type*} [Group H] [Group V]
    (f : H→*V) (himage : f.range.IsSubnormal) (N : Subgroup H) (hN : N.Normal) :
    (N.map f).IsSubnormal := by
  have hs : (N.map f.rangeRestrict).IsSubnormal :=
    hN.isSubnormal.map f.rangeRestrict_surjective
  have ht := hs.trans' himage
  simpa only [Subgroup.map_map] using ht

theorem normal_subgroup_class_card_le_coordinate_bounds
    {H : Type*} [Group H] [Finite H] (n : ℕ)
    (V : Fin n→Type*) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : Fin n→ℕ) (f : ∀i,H→*V i)
    (hc : ∀i (N : Subgroup H),N.Normal→Nat.card (ConjClasses (N.map (f i)))≤c i)
    (L : Subgroup H) (hL : L.Normal)
    (hinj : Function.Injective (fun x : L=>fun i=>f i x.val)) :
    Nat.card (ConjClasses L)≤∏i,c i := by
  induction n generalizing L with
  | zero =>
    letI : Subsingleton L := ⟨fun x y=>hinj (funext (fun i=>Fin.elim0 i))⟩
    have hh := Nat.card_le_card_of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective
    simpa only [Nat.card_unique,Fin.prod_univ_zero] using hh
  | succ n ih =>
    letI : L.Normal := hL
    let K : Subgroup H := L⊓(f 0).ker
    letI : K.Normal := by dsimp only [K]; infer_instance
    have htail : Function.Injective (fun x : K=>fun i : Fin n=>f i.succ x.val) := by
      intro x y he
      have hxy : (⟨x.val,x.property.1⟩ : L)=⟨y.val,y.property.1⟩ := by
        apply hinj
        funext i
        refine Fin.cases ?_ (fun j=>?_) i
        · exact x.property.2.trans y.property.2.symm
        · exact congrFun he j
      exact Subtype.ext (congrArg (fun z : L=>z.val) hxy)
    have hK := ih (fun i : Fin n=>V i.succ) (fun i=>c i.succ) (fun i=>f i.succ)
      (fun i N hN=>hc i.succ N hN) K inferInstance htail
    let fL : L→*V 0 := (f 0).comp L.subtype
    let e : fL.ker≃*K :=
      { toFun := fun x=>⟨x.val.val,⟨x.val.property,x.property⟩⟩
        invFun := fun x=>⟨⟨x.val,x.property.1⟩,x.property.2⟩
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl
        map_mul' := fun _ _=>rfl }
    have hker : Nat.card (ConjClasses fL.ker)≤Nat.card (ConjClasses K) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    have hrange : fL.range=L.map (f 0) := by
      dsimp only [fL]
      rw [MonoidHom.range_comp,Subgroup.range_subtype]
    have hsplit := conjugacyClass_card_le_kernel_mul_range fL
    rw [hrange] at hsplit
    rw [Fin.prod_univ_succ]
    exact hsplit.trans ((Nat.mul_le_mul (hker.trans hK) (hc 0 L hL)).trans_eq (Nat.mul_comm _ _))

theorem class_card_le_subnormal_coordinate_bounds {H : Type*} [Group H] [Finite H]
    (n : ℕ) (V : Fin n→Type*) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : Fin n→ℕ) (f : ∀i,H→*V i) (himage : ∀i,(f i).range.IsSubnormal)
    (hc : ∀i (L : Subgroup (V i)),L.IsSubnormal→Nat.card (ConjClasses L)≤c i)
    (hinj : Function.Injective (fun x=>fun i=>f i x)) :
    Nat.card (ConjClasses H)≤∏i,c i := by
  have ht := normal_subgroup_class_card_le_coordinate_bounds n V c f
    (fun i N hN=>hc i (N.map (f i)) (map_normal_isSubnormal_of_range (f i) (himage i) N hN))
    ⊤ Subgroup.normal_top (fun x y he=>Subtype.ext (hinj he))
  have he : Nat.card (ConjClasses H)≤Nat.card (ConjClasses (⊤ : Subgroup H)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup H)≃*H).toMonoidHom)
      (ConjClasses.map_surjective (Subgroup.topEquiv : (⊤ : Subgroup H)≃*H).surjective)
  exact he.trans ht

end SymmetricSubgroupAsymptotics.SubnormalCoordinateClassBound
