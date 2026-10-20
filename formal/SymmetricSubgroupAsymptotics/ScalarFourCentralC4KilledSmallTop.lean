import SymmetricSubgroupAsymptotics.ScalarFourCentralC4KilledCubic
import SymmetricSubgroupAsymptotics.C4CoordinateSurjectiveQuotient
import Mathlib.GroupTheory.Index

/-! If a quotient kills the cubic in an actual top of order six, its
remaining kernel is the image of the original central binary group and
its index divides two. The quotient can contain C4; no elementary chart
for the whole quotient is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H]
  [Finite Q] [Finite T] [Finite H] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

include D

theorem killed_small_top_card_power (hT : Nat.card T=6)
    (hcubic : orderOf D.cubic=3) (f : Q →* H) (hf : Function.Surjective f)
    (n : Q) (hn : D.top n=D.cubic) (hfn : f n=1) :
    ∃ r : ℕ, r≤2*c+1 ∧ Nat.card H=2^r := by
  let M : Subgroup H := D.top.ker.map f
  let L : Subgroup Q := D.top.ker ⊔ f.ker
  let B : Subgroup T := L.map D.top
  have hmem : D.cubic∈B := by
    exact ⟨n,(show f.ker≤L from le_sup_right) (show n∈f.ker from hfn),hn⟩
  let t : B := ⟨D.cubic,hmem⟩
  have ht : orderOf t=3 := by
    rw [←orderOf_injective B.subtype Subtype.val_injective t]
    exact hcubic
  have hdiv : 3∣Nat.card B := by
    rw [←ht]
    exact orderOf_dvd_natCard t
  have hindex : B.index∣2 := by
    obtain ⟨k,hk⟩ := hdiv
    have he := B.card_mul_index
    rw [hT,hk] at he
    have he' : k*B.index=2 := by nlinarith
    exact ⟨k,by nlinarith [he']⟩
  have hMB : M.index=B.index := by
    have hf' := Subgroup.index_map (H:=D.top.ker) f
    rw [f.range_eq_top_of_surjective hf,Subgroup.index_top,mul_one] at hf'
    have ht' := Subgroup.index_map_eq (H:=L) D.top_surjective
      (show D.top.ker≤L from le_sup_left)
    exact hf'.trans ht'.symm
  have hMindex : M.index∣2 := hMB ▸ hindex
  let q : D.active.ker →* M :=
    { toFun := fun z => ⟨f ((z : D.top.ker) : Q),
        ⟨((z : D.top.ker) : Q),(z : D.top.ker).property,rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f _ _) }
  have hq : Function.Surjective q := by
    rintro ⟨h,k,hk,rfl⟩
    obtain ⟨z,hz⟩ := D.kernel_image_central f n hn hfn ⟨k,hk⟩
    exact ⟨z,Subtype.ext hz⟩
  obtain ⟨a,ha,j,hj⟩ := C4CoordinateSurjectiveQuotient.exists_embedding
    D.centralCoordinates D.centralCoordinates_injective q hq
  have hcard : Nat.card (Fin a → Multiplicative (ZMod 4))=2^(2*a) := by
    have hh : Nat.card (Fin a → Multiplicative (ZMod 4))=4^a := by
      rw [Nat.card_fun,Nat.card_congr Multiplicative.toAdd]
      simp
    rw [hh,show (4 : ℕ)=2^2 by decide,←pow_mul]
  have hp : IsPGroup 2 (Fin a → Multiplicative (ZMod 4)) := IsPGroup.of_card hcard
  have hMgroup : IsPGroup 2 M := hp.of_injective j hj
  obtain ⟨r,hrcard⟩ := hMgroup.exists_card_eq
  have hMbound : Nat.card M≤2^(2*c) := by
    calc
      _ ≤ Nat.card (Fin a → Multiplicative (ZMod 4)) := Nat.card_le_card_of_injective j hj
      _ = 2^(2*a) := hcard
      _ ≤ 2^(2*c) := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : r≤2*c := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (hrcard ▸ hMbound)
  have hM : Nat.card M=2^r := hrcard
  have he := M.card_mul_index
  rw [hM] at he
  rcases (Nat.dvd_prime Nat.prime_two).mp hMindex with hi | hi
  · refine ⟨r,by omega,?_⟩
    simpa [hi] using he.symm
  · refine ⟨r+1,by omega,?_⟩
    simpa [hi,pow_succ] using he.symm

theorem killed_small_top_isPGroup (hT : Nat.card T=6)
    (hcubic : orderOf D.cubic=3) (f : Q →* H) (hf : Function.Surjective f)
    (n : Q) (hn : D.top n=D.cubic) (hfn : f n=1) : IsPGroup 2 H := by
  obtain ⟨r,_,hr⟩ := D.killed_small_top_card_power hT hcubic f hf n hn hfn
  exact IsPGroup.of_card hr

theorem killed_small_top_card_le (hT : Nat.card T=6)
    (hcubic : orderOf D.cubic=3) (f : Q →* H) (hf : Function.Surjective f)
    (n : Q) (hn : D.top n=D.cubic) (hfn : f n=1) : Nat.card H≤2^(2*c+1) := by
  obtain ⟨r,hr,he⟩ := D.killed_small_top_card_power hT hcubic f hf n hn hfn
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 1≤2) hr

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
