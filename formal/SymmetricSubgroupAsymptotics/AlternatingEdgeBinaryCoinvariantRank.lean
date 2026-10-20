import SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectorRanks

/-! The active rank of any actual quotient section killing Klein
commutators is at most two. The section is arbitrary and retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors

private theorem W_active : ∀ v : Vector, v ∈ W → active v = v := by decide +kernel
private theorem active_square : ∀ v : Vector, active (active v) = active v := by decide +kernel

theorem quotient_active_rank_le_two
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [FiniteDimensional (ZMod 2) Q]
    (K : Submodule (ZMod 2) Vector)
    (hK : ∀ v ∈ K, A v ∈ K)
    (hD : ∀ d v, v ∈ K → difference d v ∈ K)
    (q : K →ₗ[ZMod 2] Q) (hq : Function.Surjective q)
    (T : Module.End (ZMod 2) Q)
    (hint : ∀ v : K, q ⟨A v,hK v v.property⟩ = T (q v))
    (hkill : ∀ (d : Fin 3) (v : K), q ⟨difference d v,hD d v v.property⟩ = 0) :
    Module.finrank (ZMod 2) (T+T^2).range ≤ 2 := by
  have hactive (v : Vector) (hv : v ∈ K) : active v ∈ K :=
    K.add_mem (hK v hv) (hK (A v) (hK v hv))
  have q_active (v : K) : q ⟨active v,hactive v v.property⟩ = (T+T^2) (q v) := by
    change q (⟨A v,hK v v.property⟩ +
      ⟨A (A v),hK (A v) (hK v v.property)⟩) = T (q v)+T (T (q v))
    rw [map_add, hint v]
    have hi := hint (⟨A v,hK v v.property⟩ : K)
    change q ⟨A (A v),hK (A v) (hK v v.property)⟩ = T (q ⟨A v,hK v v.property⟩) at hi
    rw [hi, hint v]
  let J : Submodule (ZMod 2) Vector := q.ker.map K.subtype
  have hJK : J ≤ K := by
    rintro v ⟨k,_hk,rfl⟩
    exact k.property
  have hqJ (v : K) (hv : v.val ∈ J) : q v = 0 := by
    obtain ⟨k,hk,he⟩ := hv
    have he' : k = v := Subtype.ext he
    rw [← he']
    exact hk
  have hJ : ∀ v ∈ J, A v ∈ J := by
    rintro v ⟨k,hk,rfl⟩
    refine ⟨⟨A k,hK k k.property⟩,?_,rfl⟩
    change q ⟨A k,hK k k.property⟩ = 0
    rw [hint,show q k = 0 from hk,map_zero]
  have hcomm : ∀ v ∈ K, ∀ d : Fin 3, active (difference d v) ∈ J := by
    intro v hv d
    let k : K := ⟨difference d v,hD d v hv⟩
    refine ⟨⟨active k,hactive k k.property⟩,?_,rfl⟩
    change q ⟨active k,hactive k k.property⟩ = 0
    rw [q_active,show q k = 0 from hkill d ⟨v,hv⟩,map_zero]
  let L : Submodule (ZMod 2) Vector := K ⊓ active.range
  have hLfixed (v : L) : active v = v := by
    obtain ⟨w,hw⟩ := v.property.2
    rw [← hw]
    exact active_square w
  let f : L →ₗ[ZMod 2] (T+T^2).range :=
    { toFun := fun v => ⟨q ⟨v,v.property.1⟩,⟨q ⟨v,v.property.1⟩,by
        exact (q_active ⟨v,v.property.1⟩).symm.trans
          (congrArg q (Subtype.ext (hLfixed v)))⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change q ((⟨x,x.property.1⟩ : K) + ⟨y,y.property.1⟩) = _
        exact q.map_add _ _
      map_smul' := by
        intro c x
        apply Subtype.ext
        change q (c • (⟨x,x.property.1⟩ : K)) = _
        exact q.map_smul c _ }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨v,hv⟩ := y.property
    obtain ⟨k,hk⟩ := hq v
    refine ⟨⟨active k, hactive k k.property, k,rfl⟩,?_⟩
    apply Subtype.ext
    change q ⟨active k,hactive k k.property⟩ = y.val
    rw [q_active,hk]
    exact hv
  have hdim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf,finrank_top] at hdim
  rcases active_subspace_or_plane_le K J hK hJ hcomm with hsmall | hlarge
  · let e : L →ₗ[ZMod 2] W := L.subtype.codRestrict W (fun v => by
      change v.val ∈ W
      rw [← hLfixed v]
      exact hsmall v v.property.1)
    have he : Function.Injective e := fun _ _ h =>
      Subtype.ext (congrArg (fun z : W => z.val) h)
    have hle := e.finrank_le_finrank_of_injective he
    rw [W_finrank] at hle
    omega
  · let e : W →ₗ[ZMod 2] L := W.subtype.codRestrict L (fun w =>
      ⟨hJK (hlarge w.property),⟨w,W_active w w.property⟩⟩)
    let ek : W →ₗ[ZMod 2] f.ker := e.codRestrict f.ker (fun w => by
      apply Subtype.ext
      exact hqJ ⟨w,hJK (hlarge w.property)⟩ (hlarge w.property))
    have hek : Function.Injective ek := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : f.ker => (z.val.val : Vector)) h)
    have hker := ek.finrank_le_finrank_of_injective hek
    rw [W_finrank] at hker
    let er : L →ₗ[ZMod 2] active.range :=
      L.subtype.codRestrict active.range (fun v => v.property.2)
    have her : Function.Injective er := fun _ _ h =>
      Subtype.ext (congrArg (fun z : active.range => z.val) h)
    have hL := (er.finrank_le_finrank_of_injective her).trans active_rank_le_four
    omega

end SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors
