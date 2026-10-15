import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.PairLocalQuotientExtension
import SymmetricSubgroupAsymptotics.TernaryLocalBinaryRadical

/-!
# The actual local map descends through a nontrivial pair kernel

A nontrivial normal pair kernel flips every original pair in a transitive
physical action. Thus the original point stabilizer maps onto the stabilizer
of its pair in the faithful pair top. Its kernel is binary, and an onto
C3/noncommutative-order-six local map kills it. The descended map and its
extension to the original pair stabilizer retain the original local target.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) [MulAction.IsPretransitive U X]

/-- A nontrivial correlated pair kernel contains a flip at each pair.
The flipping element can depend on the pair; no full base group is assumed. -/
theorem exists_kernel_bit_one (hker : F.top.ker ≠ ⊥) (i : I) :
    ∃ k : F.top.ker, F.bits k i = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  obtain ⟨j, hj⟩ : ∃ j : I, F.bits k j ≠ 0 := by
    by_contra! hall
    apply hk
    apply F.bitsHom_injective
    calc
      F.bitsHom k = 1 := by
        change Multiplicative.ofAdd (F.bits k) = Multiplicative.ofAdd 0
        apply congrArg Multiplicative.ofAdd
        funext j
        exact hall j
      _ = F.bitsHom 1 := F.bitsHom.map_one.symm
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  have hj1 : F.bits k j = 1 := (hbits _).resolve_left hj
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U
    (F.frame (j, 0)) (F.frame (i, 0))
  have htop : F.top u j = i := by
    have h := F.intertwine u (j, 0)
    change (F.frame.symm (u • F.frame (j, 0))).1 = F.top u j at h
    rw [hu, Equiv.symm_apply_apply] at h
    exact h.symm
  have hinv : (F.top u)⁻¹ i = j := by
    rw [← htop]
    exact Equiv.symm_apply_apply (F.top u) j
  refine ⟨MulAut.conjNormal u k, ?_⟩
  rw [F.bits_conjNormal, hinv, hj1]

/-- Every bit occurs at each coordinate of the actual kernel. -/
theorem kernel_bit_surjective (hker : F.top.ker ≠ ⊥) (i : I) :
    Function.Surjective (fun k : F.top.ker => F.bits k i) := by
  intro b
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  rcases hbits b with rfl | rfl
  · refine ⟨1, ?_⟩
    exact congrArg (fun z : Multiplicative (I → ZMod 2) => z.toAdd i)
      F.bitsHom.map_one
  · exact F.exists_kernel_bit_one hker i

abbrev pointStabilizer (i : I) : Subgroup U :=
  MulAction.stabilizer U (F.frame (i, 0))

abbrev pairTopStabilizer (i : I) : Subgroup F.top.range :=
  MulAction.stabilizer F.top.range i

/-- The original pair stabilizer, before quotienting its pair kernel. -/
def pairStabilizer (i : I) : Subgroup U :=
  (F.pairTopStabilizer i).comap F.top.rangeRestrict

omit [MulAction.IsPretransitive U X] in
theorem pointStabilizer_le_pairStabilizer (i : I) :
    F.pointStabilizer i ≤ F.pairStabilizer i := by
  intro u hu
  change F.top u i = i
  have h := F.intertwine u (i, 0)
  change (F.frame.symm (u • F.frame (i, 0))).1 = F.top u i at h
  rw [show u • F.frame (i, 0) = F.frame (i, 0) from hu,
    Equiv.symm_apply_apply] at h
  exact h.symm

def pairStabilizerTopMap (i : I) :
    F.pairStabilizer i →* F.pairTopStabilizer i where
  toFun u := ⟨F.top.rangeRestrict u.1, u.2⟩
  map_one' := Subtype.ext F.top.rangeRestrict.map_one
  map_mul' u v := Subtype.ext (F.top.rangeRestrict.map_mul u.1 v.1)

def pointStabilizerTopMap (i : I) :
    F.pointStabilizer i →* F.pairTopStabilizer i :=
  (F.pairStabilizerTopMap i).comp
    (Subgroup.inclusion (F.pointStabilizer_le_pairStabilizer i))

/-- Correcting an arbitrary lift by an actual kernel element makes it fix
its chosen original point. This proves onto-ness without choosing a split. -/
theorem pointStabilizerTopMap_surjective
    (hker : F.top.ker ≠ ⊥) (i : I) :
    Function.Surjective (F.pointStabilizerTopMap i) := by
  intro t
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t.1
  have hui : F.top u i = i := by
    change F.top.rangeRestrict u • i = i
    rw [hu]
    exact t.property
  obtain ⟨k, hk⟩ := F.kernel_bit_surjective hker i (F.offset u i)
  change F.bits k i = F.offset u i at hk
  let v : U := (k : U) * u
  have hv : v ∈ F.pointStabilizer i := by
    change ((k : U) : Equiv.Perm X) ((u : Equiv.Perm X) (F.frame (i, 0))) =
      F.frame (i, 0)
    rw [F.action_frame, hui, zero_add, F.kernel_action_frame, hk]
    have hsum : ∀ b : ZMod 2, b + b = 0 := by decide +kernel
    rw [hsum]
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change F.top ((k : U) * u) = (t.1 : Equiv.Perm I)
  rw [map_mul, MonoidHom.mem_ker.mp k.property, one_mul]
  exact congrArg Subtype.val hu

/-- The kernel of the actual point-stabilizer map embeds in the original
correlated pair kernel. -/
theorem pointStabilizerTopMap_kernel_binary (i : I) :
    IsPGroup 2 (F.pointStabilizerTopMap i).ker := by
  let j : (F.pointStabilizerTopMap i).ker →* F.top.ker := {
    toFun h := ⟨h.1.1, by
      have heq := congrArg (fun t : F.pairTopStabilizer i =>
        ((t : F.top.range) : Equiv.Perm I)) h.property
      exact heq⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply F.kernel_isPGroup.of_injective j
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun k : F.top.ker => (k : U)) hab

variable {C : Type} [Group C] [Finite C]

/-- The actual onto local map kills the point-stabilizer pair kernel. -/
theorem pointStabilizerTopMap_kernel_le
    (i : I) (f : F.pointStabilizer i →* C)
    (hf : Function.Surjective f)
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C)) :
    (F.pointStabilizerTopMap i).ker ≤ f.ker :=
  binary_normal_le_kernel_of_ternary_local f hf hC _
    (F.pointStabilizerTopMap_kernel_binary i)

/-- The unchanged local target, now as an actual quotient of the pair-top
stabilizer. -/
def descendedPointLocalMap (hker : F.top.ker ≠ ⊥) (i : I)
    (f : F.pointStabilizer i →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C)) :
    F.pairTopStabilizer i →* C :=
  PairLocalQuotientExtension.descended
    (Subgroup.inclusion (F.pointStabilizer_le_pairStabilizer i))
    (F.pairStabilizerTopMap i) f
    (F.pointStabilizerTopMap_surjective hker i)
    (F.pointStabilizerTopMap_kernel_le i f hf hC)

theorem descendedPointLocalMap_surjective
    (hker : F.top.ker ≠ ⊥) (i : I)
    (f : F.pointStabilizer i →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C)) :
    Function.Surjective (F.descendedPointLocalMap hker i f hf hC) :=
  PairLocalQuotientExtension.descended_surjective _ _ _ _ _ hf

/-- The commuting square binds the descended map to the supplied original
local map, not merely to an isomorphic target. -/
theorem descendedPointLocalMap_comp
    (hker : F.top.ker ≠ ⊥) (i : I)
    (f : F.pointStabilizer i →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C)) :
    (F.descendedPointLocalMap hker i f hf hC).comp
      (F.pointStabilizerTopMap i) = f := by
  ext h
  exact PairLocalQuotientExtension.descended_apply _ _ _ _ _ h

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
