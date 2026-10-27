import SymmetricSubgroupAsymptotics.InjectiveCosetProjectionFibreIndex
import SymmetricSubgroupAsymptotics.EquivariantOrbitFibreExact

/-! Exact orbit scaling for an actual correlated coset cover. The only
transport requirement is on the actual stabilizer fibre, not an independent
coordinate action or a normal subgroup of the whole ambient group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CosetOrbitFibreScaling
variable {A G : Type} [Group A] [Group G]

theorem card_orbit_eq_index_mul [Finite G]
    (f : A →* G) (hf : Function.Injective f) (H : Subgroup A) (g : G)
    (hfill : ∀ b : A, ∃ a : A,
      (QuotientGroup.mk (f a*g) : G ⧸ H.map f) = QuotientGroup.mk (g*f b)) :
    letI : MulAction A (G ⧸ H.map f) := MulAction.compHom _ f
    letI : MulAction A (G ⧸ f.range) := MulAction.compHom _ f
    Nat.card (MulAction.orbit A (QuotientGroup.mk g : G ⧸ H.map f)) =
      H.index * Nat.card (MulAction.orbit A (QuotientGroup.mk g : G ⧸ f.range)) := by
  classical
  letI : MulAction A (G ⧸ H.map f) := MulAction.compHom _ f
  letI : MulAction A (G ⧸ f.range) := MulAction.compHom _ f
  have hle : H.map f ≤ f.range := by rintro _ ⟨a,_,rfl⟩; exact ⟨a,rfl⟩
  let b : (G ⧸ H.map f) → (G ⧸ f.range) := Subgroup.quotientMapOfLE hle
  let x : G ⧸ H.map f := QuotientGroup.mk g
  have hb (a : A) (y : G ⧸ H.map f) : b (a • y)=a • b y := by
    induction y using Quotient.inductionOn' with
    | h y => rfl
  let K : Subgroup A := MulAction.stabilizer A (b x)
  have hK (k : K) : (k : A) • b x=b x := k.property
  have fill (y : G ⧸ H.map f) (hy : b y=b x) : y ∈ MulAction.orbit K x := by
    induction y using Quotient.inductionOn' with
    | h v =>
      have hvg : v⁻¹*g ∈ f.range := QuotientGroup.eq.mp hy
      have hgv : g⁻¹*v ∈ f.range := by
        simpa only [mul_inv_rev,inv_inv] using f.range.inv_mem hvg
      obtain ⟨c,hc⟩ := hgv
      have hv : g*f c=v := by rw [hc,mul_inv_cancel_left]
      obtain ⟨a,ha⟩ := hfill c
      have hax : a • x=(QuotientGroup.mk v : G ⧸ H.map f) := by
        change (QuotientGroup.mk (f a*g) : G ⧸ H.map f)=QuotientGroup.mk v
        simpa only [hv] using ha
      have hak : a ∈ K := by
        change a • b x=b x
        rw [←hb,hax]
        exact hy
      exact MulAction.mem_orbit_iff.mpr ⟨⟨a,hak⟩,hax⟩
  let e : MulAction.orbit K x ≃ {y : G ⧸ H.map f // b y=b x} :=
    { toFun := fun y => ⟨y.val,by
        obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp y.property
        rw [←hk]
        change b ((k : A) • x)=b x
        exact (hb (k : A) x).trans (hK k)⟩
      invFun := fun y => ⟨y.val,fill y.val y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Nat.card (MulAction.orbit K x)=H.index :=
    (Nat.card_congr e).trans (InjectiveCosetProjectionFibreIndex.card_fibre_eq_index f hf H (b x))
  have hscale := EquivariantOrbitFibreExact.orbit_card_eq_block_mul_fibre
    (G:=A) (X:=G ⧸ H.map f) (I:=G ⧸ f.range) b hb K x hK fill
  rw [hcard] at hscale
  change Nat.card (MulAction.orbit A (QuotientGroup.mk g : G ⧸ H.map f)) =
    Nat.card (MulAction.orbit A (QuotientGroup.mk g : G ⧸ f.range))*H.index at hscale
  exact hscale.trans (Nat.mul_comm _ _)

end SymmetricSubgroupAsymptotics.CosetOrbitFibreScaling
