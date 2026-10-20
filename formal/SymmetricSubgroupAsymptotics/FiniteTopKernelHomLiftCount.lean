import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import SymmetricSubgroupAsymptotics.BinaryTargetOrderEnvelope

/-! Generic nonsplit lift counting above one actual finite top map.
Restriction to the SAME source kernel and evaluations on actual chosen
coset representatives recover every original map. No centrality or
splitting is required; small binary targets may include C4. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
variable {Q T J : Type} [Group Q] [Group T] [Group J]
  [Finite Q] [Finite T] [Finite J]
  (top : Q →* T) (theta : J →* T)

abbrev Fibre := {phi : GroupEpimorphism J Q // top.comp phi.val=theta}

/-- All actual top-section values are charged once. -/
theorem fixed_top_card_le (htheta : Function.Surjective theta) :
    Nat.card (Fibre top theta)≤
      Nat.card Q^Nat.card T*Nat.card (theta.ker →* top.ker) := by
  choose s hs using htheta
  let F := theta.ker
  let L := Fibre top theta
  let restrict : L → (F →* top.ker) := fun phi =>
    (phi.val.val.comp F.subtype).codRestrict top.ker (by
      intro f
      change top (phi.val.val (f : J))=1
      have he := DFunLike.congr_fun phi.property (f : J)
      change top (phi.val.val (f : J))=theta (f : J) at he
      exact he.trans f.property)
  let eval : L → (T → Q) := fun phi t => phi.val.val (s t)
  let code : L → (T → Q) × (F →* top.ker) := fun phi => (eval phi,restrict phi)
  have hi : Function.Injective code := by
    intro phi chi h
    have he : eval phi=eval chi := congrArg Prod.fst h
    have hr : restrict phi=restrict chi := congrArg Prod.snd h
    apply Subtype.ext
    apply Subtype.ext
    apply MonoidHom.ext
    intro g
    let t := theta g
    have hm : (s t)⁻¹*g∈F := by
      change theta ((s t)⁻¹*g)=1
      rw [map_mul,map_inv,hs]
      exact inv_mul_cancel t
    have hf := congrArg Subtype.val (DFunLike.congr_fun hr ⟨_,hm⟩)
    change phi.val.val ((s t)⁻¹*g)=chi.val.val ((s t)⁻¹*g) at hf
    have hv := congrFun he t
    change phi.val.val (s t)=chi.val.val (s t) at hv
    rw [map_mul,map_inv,map_mul,map_inv,hv] at hf
    exact mul_left_cancel hf
  letI : Finite (F →* top.ker) := Finite.of_injective
    (fun f : F →* top.ker => (f : F → top.ker)) DFunLike.coe_injective
  calc
    _ ≤ Nat.card ((T → Q) × (F →* top.ker)) := Nat.card_le_card_of_injective code hi
    _ = _ := by rw [Nat.card_prod,Nat.card_fun]

/-- The binary rank belongs to the actual index-|T| source kernel. -/
theorem fixed_top_binary_card_le (htheta : Function.Surjective theta)
    (hK : IsPGroup 2 top.ker) (m : ℕ) (hcard : Nat.card top.ker≤2^m) :
    Nat.card (Fibre top theta)≤Nat.card Q^Nat.card T*
      2^(m*binaryCharacterRank theta.ker) := by
  have hh := binaryTargetOrder_hom_card_le (J := theta.ker) hK
  have hl : Nat.log 2 (Nat.card top.ker) ≤ m := by
    exact (Nat.log_mono_right (b := 2) hcard).trans_eq (Nat.log_pow (by norm_num) m)
  exact (fixed_top_card_le top theta htheta).trans
    (Nat.mul_le_mul_left _ (hh.trans (Nat.pow_le_pow_right (by decide : 1≤2)
      (Nat.mul_le_mul_right _ hl))))

end SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
