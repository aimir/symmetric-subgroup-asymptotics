import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy
import SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality

/-! A central extension with an actual nondegenerate scalar commutator
pairing has the same sharp centre-proper index bound as a Heisenberg
group. No recognition isomorphism is needed. The central intersection
and vector image belong to the same literal subgroup, and are restricted
only to the prime field, never assumed linear over the full field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex

variable {F V N : Type*} [Field F] [AddCommGroup V] [Module F V] [Group N]

structure Data where
  projection : N →* Multiplicative V
  central : Multiplicative F →* N
  central_injective : Function.Injective central
  central_range : central.range = projection.ker
  projection_surjective : Function.Surjective projection
  pairing : V →ₗ[F] V →ₗ[F] F
  alternating : ∀ v, pairing v v = 0
  full : ∀ v, v ≠ 0 → Function.Surjective (pairing v)
  commutator : ∀ x y : N, x*y*x⁻¹*y⁻¹ =
    central (Multiplicative.ofAdd (pairing (projection x).toAdd (projection y).toAdd))

namespace Data

def vectorImage (D : Data (F := F) (V := V) (N := N)) (L : Subgroup N) :
    AddSubgroup V := (L.map D.projection).toAddSubgroup'

def centralPreimage (D : Data (F := F) (V := V) (N := N)) (L : Subgroup N) :
    AddSubgroup F := (L.comap D.central).toAddSubgroup'

theorem centralPreimage_ne_top (D : Data (F := F) (V := V) (N := N))
    (L : Subgroup N) (hL : ¬D.central.range ≤ L) : D.centralPreimage L ≠ ⊤ := by
  intro he
  apply hL
  rintro x ⟨z,rfl⟩
  change z.toAdd ∈ D.centralPreimage L
  rw [he]
  trivial

theorem pairing_mem_centralPreimage (D : Data (F := F) (V := V) (N := N))
    (L : Subgroup N) (v : V) (hv : v ∈ D.vectorImage L)
    (w : V) (hw : w ∈ D.vectorImage L) :
    D.pairing v w ∈ D.centralPreimage L := by
  change Multiplicative.ofAdd v ∈ L.map D.projection at hv
  change Multiplicative.ofAdd w ∈ L.map D.projection at hw
  obtain ⟨x,hx,hxv⟩ := hv
  obtain ⟨y,hy,hyw⟩ := hw
  have hxv' : (D.projection x).toAdd = v := congrArg Multiplicative.toAdd hxv
  have hyw' : (D.projection y).toAdd = w := congrArg Multiplicative.toAdd hyw
  change D.central (Multiplicative.ofAdd (D.pairing v w)) ∈ L
  rw [←hxv',←hyw',←D.commutator]
  exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)

theorem vectorImage_card_le [Finite F] [Finite V]
    (D : Data (F := F) (V := V) (N := N))
    (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hdim : Module.finrank F V = 2*m)
    (L : Subgroup N) (hL : ¬D.central.range ≤ L) :
    Nat.card (D.vectorImage L) ≤ Nat.card F^m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Module (ZMod p) V := Module.restrictScalars (ZMod p) F V
  letI : IsScalarTower (ZMod p) F V := IsScalarTower.restrictScalars (ZMod p) F V
  letI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let B := D.pairing.restrictScalars₁₂ (ZMod p) (ZMod p)
  let W := D.vectorImage L
  let C := D.centralPreimage L
  let A := AddSubgroup.toZModSubmodule p W
  have hd : 2*Module.finrank (ZMod p) A ≤ Module.finrank (ZMod p) V :=
    CFSGHeisenbergCentralIsotropy.additive_twice_finrank_le p B
      D.alternating D.full C (D.centralPreimage_ne_top L hL) W
      (fun v hv w hw => D.pairing_mem_centralPreimage L v hv w hw)
  have hW : Nat.card W = p^Module.finrank (ZMod p) A := by
    change Nat.card A = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  have hV : Nat.card V = p^Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  have hs : Nat.card W^2 ≤ Nat.card V := by
    rw [hW,hV,←pow_mul]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (by simpa only [Nat.mul_comm] using hd)
  have hv : Nat.card V = (Nat.card F^m)^2 := by
    rw [Module.natCard_eq_pow_finrank (K := F),hdim,←pow_mul]
    congr 1
    omega
  rw [hv] at hs
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hs

theorem subgroup_card_mul_prime_le [Finite F] [Finite V] [Finite N]
    (D : Data (F := F) (V := V) (N := N))
    (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hdim : Module.finrank F V = 2*m)
    (L : Subgroup N) (hL : ¬D.central.range ≤ L) :
    p*Nat.card L ≤ Nat.card F^(m+1) := by
  have he := ExactHomSubgroupCardinality.card_comap_mul_card_map
    D.projection D.central D.central_injective D.central_range L
  have he' : Nat.card (D.centralPreimage L)*Nat.card (D.vectorImage L) = Nat.card L := he
  rw [←he']
  calc
    p*(Nat.card (D.centralPreimage L)*Nat.card (D.vectorImage L)) =
        (p*Nat.card (D.centralPreimage L))*Nat.card (D.vectorImage L) :=
      (Nat.mul_assoc _ _ _).symm
    _ ≤ Nat.card F*Nat.card F^m := Nat.mul_le_mul
      (CFSGHeisenbergFiniteFieldIsotropy.proper_additive_card_mul_prime_le p _
        (D.centralPreimage_ne_top L hL))
      (D.vectorImage_card_le p m hdim L hL)
    _ = Nat.card F^(m+1) := by rw [pow_succ,Nat.mul_comm]

theorem card_eq [Finite F] [Finite V] [Finite N]
    (D : Data (F := F) (V := V) (N := N)) (m : ℕ)
    (hdim : Module.finrank F V = 2*m) : Nat.card N = Nat.card F^(2*m+1) := by
  have he := ExactHomSubgroupCardinality.card_comap_mul_card_map
    D.projection D.central D.central_injective D.central_range (⊤ : Subgroup N)
  rw [Subgroup.comap_top,Subgroup.map_top_of_surjective _ D.projection_surjective,
    Subgroup.card_top,Subgroup.card_top,Subgroup.card_top] at he
  change Nat.card F*Nat.card V = Nat.card N at he
  rw [Module.natCard_eq_pow_finrank (K := F) (V := V),hdim] at he
  exact he.symm.trans (by rw [pow_succ,Nat.mul_comm])

theorem index_least [Finite F] [Finite V] [Finite N]
    (D : Data (F := F) (V := V) (N := N))
    (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hdim : Module.finrank F V = 2*m)
    (L : Subgroup N) (hL : ¬D.central.range ≤ L) :
    p*Nat.card F^m ≤ L.index := by
  have hs := D.subgroup_card_mul_prime_le p m hdim L hL
  have he := L.card_mul_index
  rw [D.card_eq m hdim] at he
  apply Nat.le_of_mul_le_mul_left _ (pow_pos (Nat.card_pos (α := F)) (m+1))
  calc
    Nat.card F^(m+1)*(p*Nat.card F^m) = p*Nat.card F^(2*m+1) := by
      rw [←Nat.mul_assoc,Nat.mul_comm (Nat.card F^(m+1)) p,Nat.mul_assoc,←pow_add]
      rw [show m+1+m=2*m+1 by omega]
    _ = (p*Nat.card L)*L.index := by rw [←he,Nat.mul_assoc]
    _ ≤ Nat.card F^(m+1)*L.index := Nat.mul_le_mul_right L.index hs

theorem degree_le_of_central_motion [Finite F] [Finite V] [Finite N]
    (D : Data (F := F) (V := V) (N := N))
    (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hdim : Module.finrank F V = 2*m)
    {X : Type*} [Finite X] [MulAction N X]
    (x : X) (c : Multiplicative F) (hc : D.central c • x ≠ x) :
    p*Nat.card F^m ≤ Nat.card X := by
  have hL : ¬D.central.range ≤ MulAction.stabilizer N x := by
    intro hh
    exact hc (hh ⟨c,rfl⟩)
  calc
    p*Nat.card F^m ≤ (MulAction.stabilizer N x).index := D.index_least p m hdim _ hL
    _ = (MulAction.orbit N x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

end Data
end SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex
