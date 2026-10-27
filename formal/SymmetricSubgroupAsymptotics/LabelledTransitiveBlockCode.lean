import SymmetricSubgroupAsymptotics.LabelledMinimalBlockWreathCover
import SymmetricSubgroupAsymptotics.FinitePermutationalWreathInstance
import Mathlib.Data.Finite.Sigma

/-! A finite reversible labelled cover of ALL transitive subgroups.
Each imprimitive code retains exactly one top subgroup, one primitive
local subgroup, one whole full-component wreath subgroup and a point
bijection. The kernel/wreath cardinality will be bounded separately. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LabelledTransitiveBlockCode

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

abbrev Primitive (n : ℕ) :=
  {R : Subgroup (Equiv.Perm (Fin n)) // MulAction.IsPreprimitive R (Fin n)}
abbrev Transitive (n : ℕ) :=
  {Q : Subgroup (Equiv.Perm (Fin n)) // MulAction.IsPretransitive Q (Fin n)}
abbrev Width (n : ℕ) := {r : Fin (n+1) // 2 ≤ r.val}

abbrev BlockCode (n : ℕ) :=
  Σ r : Width n,Σ t : Width n,Σ R : Primitive r.val.val,Σ Q : Transitive t.val.val,
    (Fin n ≃ Fin r.val.val × Fin t.val.val) ×
      ActualFullWreathFamily.Family R.val Q.val (Fin t.val.val)

def blockDecode {n : ℕ} : BlockCode n → Subgroup (Equiv.Perm (Fin n))
  | ⟨_,_,R,Q,e,L⟩ => L.val.map (LabelledMinimalBlockWreathCover.decodeHom R.val Q.val e)

theorem exists_blockCode {n : ℕ} (hn : 2 ≤ n) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (himp : ¬MulAction.IsPreprimitive J (Fin n)) :
    ∃ c : BlockCode n,blockDecode c=J := by
  obtain ⟨r,t,hr,ht,hprod,R,hR,Q,hQ,L,e,he⟩ :=
    LabelledMinimalBlockWreathCover.exists_chart hn J himp
  have hrn : r < n+1 := Nat.lt_succ_of_le
    ((Nat.le_mul_of_pos_right r (by omega : 0 < t)).trans_eq hprod)
  have htn : t < n+1 := Nat.lt_succ_of_le
    ((Nat.le_mul_of_pos_left t (by omega : 0 < r)).trans_eq hprod)
  exact ⟨⟨⟨⟨r,hrn⟩,hr⟩,⟨⟨t,htn⟩,ht⟩,⟨R,hR⟩,⟨Q,hQ⟩,e,L⟩,he⟩

abbrev Code (n : ℕ) := Primitive n ⊕ BlockCode n

def decode {n : ℕ} : Code n → Subgroup (Equiv.Perm (Fin n))
  | Sum.inl R => R.val
  | Sum.inr c => blockDecode c

theorem exists_code {n : ℕ} (hn : 2 ≤ n) (J : Transitive n) :
    ∃ c : Code n,decode c=J.val := by
  letI : MulAction.IsPretransitive J.val (Fin n) := J.property
  by_cases hp : MulAction.IsPreprimitive J.val (Fin n)
  · exact ⟨Sum.inl ⟨J.val,hp⟩,rfl⟩
  · obtain ⟨c,hc⟩ := exists_blockCode hn J.val hp
    exact ⟨Sum.inr c,hc⟩

def encode {n : ℕ} (hn : 2 ≤ n) (J : Transitive n) : Code n :=
  Classical.choose (exists_code hn J)

theorem decode_encode {n : ℕ} (hn : 2 ≤ n) (J : Transitive n) :
    decode (encode hn J)=J.val := Classical.choose_spec (exists_code hn J)

theorem encode_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (encode hn) := by
  intro J K h
  apply Subtype.ext
  exact (decode_encode hn J).symm.trans
    ((congrArg decode h).trans (decode_encode hn K))

theorem card_transitive_le {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Transitive n) ≤ Nat.card (Primitive n)+Nat.card (BlockCode n) := by
  have hi := Nat.card_le_card_of_injective (encode hn) (encode_injective hn)
  simpa only [Nat.card_sum] using hi

end SymmetricSubgroupAsymptotics.LabelledTransitiveBlockCode
