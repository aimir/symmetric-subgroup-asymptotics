import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.Tactic.FinCases

/-! Exactly32 fixed positive-word nodes for the selected J2 binary-frame recovery. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
def node000 {G : Type*} [Monoid G] (a b : G) : G := a
def node001 {G : Type*} [Monoid G] (a b : G) : G := b
def node002 {G : Type*} [Monoid G] (a b : G) : G := 1
theorem map_node000 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node000 a b)=node000 (f a) (f b) := rfl
theorem map_node001 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node001 a b)=node001 (f a) (f b) := rfl
theorem map_node002 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node002 a b)=node002 (f a) (f b) := map_one f
def node003 {G : Type*} [Monoid G] (a b : G) : G := node001 a b*node001 a b
theorem map_node003 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node003 a b)=node003 (f a) (f b) := by
  change f (node001 a b*node001 a b)=node001 (f a) (f b)*node001 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node001 f a b) (map_node001 f a b))
def node004 {G : Type*} [Monoid G] (a b : G) : G := node003 a b*node000 a b
theorem map_node004 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node004 a b)=node004 (f a) (f b) := by
  change f (node003 a b*node000 a b)=node003 (f a) (f b)*node000 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node003 f a b) (map_node000 f a b))
def node005 {G : Type*} [Monoid G] (a b : G) : G := node004 a b*node001 a b
theorem map_node005 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node005 a b)=node005 (f a) (f b) := by
  change f (node004 a b*node001 a b)=node004 (f a) (f b)*node001 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node004 f a b) (map_node001 f a b))
def node006 {G : Type*} [Monoid G] (a b : G) : G := node000 a b*node005 a b
theorem map_node006 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node006 a b)=node006 (f a) (f b) := by
  change f (node000 a b*node005 a b)=node000 (f a) (f b)*node005 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node000 f a b) (map_node005 f a b))
def node007 {G : Type*} [Monoid G] (a b : G) : G := node006 a b*node006 a b
theorem map_node007 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node007 a b)=node007 (f a) (f b) := by
  change f (node006 a b*node006 a b)=node006 (f a) (f b)*node006 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node006 f a b) (map_node006 f a b))
def node008 {G : Type*} [Monoid G] (a b : G) : G := node007 a b*node006 a b
theorem map_node008 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node008 a b)=node008 (f a) (f b) := by
  change f (node007 a b*node006 a b)=node007 (f a) (f b)*node006 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node007 f a b) (map_node006 f a b))
def node009 {G : Type*} [Monoid G] (a b : G) : G := node008 a b*node008 a b
theorem map_node009 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node009 a b)=node009 (f a) (f b) := by
  change f (node008 a b*node008 a b)=node008 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node008 f a b) (map_node008 f a b))
def node010 {G : Type*} [Monoid G] (a b : G) : G := node009 a b*node008 a b
theorem map_node010 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node010 a b)=node010 (f a) (f b) := by
  change f (node009 a b*node008 a b)=node009 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node009 f a b) (map_node008 f a b))
def node011 {G : Type*} [Monoid G] (a b : G) : G := node003 a b*node008 a b
theorem map_node011 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node011 a b)=node011 (f a) (f b) := by
  change f (node003 a b*node008 a b)=node003 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node003 f a b) (map_node008 f a b))
def node012 {G : Type*} [Monoid G] (a b : G) : G := node011 a b*node001 a b
theorem map_node012 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node012 a b)=node012 (f a) (f b) := by
  change f (node011 a b*node001 a b)=node011 (f a) (f b)*node001 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node011 f a b) (map_node001 f a b))
def node013 {G : Type*} [Monoid G] (a b : G) : G := node012 a b*node012 a b
theorem map_node013 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node013 a b)=node013 (f a) (f b) := by
  change f (node012 a b*node012 a b)=node012 (f a) (f b)*node012 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node012 f a b) (map_node012 f a b))
def node014 {G : Type*} [Monoid G] (a b : G) : G := node013 a b*node012 a b
theorem map_node014 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node014 a b)=node014 (f a) (f b) := by
  change f (node013 a b*node012 a b)=node013 (f a) (f b)*node012 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node013 f a b) (map_node012 f a b))
def node015 {G : Type*} [Monoid G] (a b : G) : G := node002 a b*node005 a b
theorem map_node015 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node015 a b)=node015 (f a) (f b) := by
  change f (node002 a b*node005 a b)=node002 (f a) (f b)*node005 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node002 f a b) (map_node005 f a b))
def node016 {G : Type*} [Monoid G] (a b : G) : G := node015 a b*node012 a b
theorem map_node016 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node016 a b)=node016 (f a) (f b) := by
  change f (node015 a b*node012 a b)=node015 (f a) (f b)*node012 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node015 f a b) (map_node012 f a b))
def node017 {G : Type*} [Monoid G] (a b : G) : G := node016 a b*node012 a b
theorem map_node017 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node017 a b)=node017 (f a) (f b) := by
  change f (node016 a b*node012 a b)=node016 (f a) (f b)*node012 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node016 f a b) (map_node012 f a b))
def node018 {G : Type*} [Monoid G] (a b : G) : G := node017 a b*node012 a b
theorem map_node018 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node018 a b)=node018 (f a) (f b) := by
  change f (node017 a b*node012 a b)=node017 (f a) (f b)*node012 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node017 f a b) (map_node012 f a b))
def node019 {G : Type*} [Monoid G] (a b : G) : G := node018 a b*node000 a b
theorem map_node019 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node019 a b)=node019 (f a) (f b) := by
  change f (node018 a b*node000 a b)=node018 (f a) (f b)*node000 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node018 f a b) (map_node000 f a b))
def node020 {G : Type*} [Monoid G] (a b : G) : G := node019 a b*node008 a b
theorem map_node020 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node020 a b)=node020 (f a) (f b) := by
  change f (node019 a b*node008 a b)=node019 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node019 f a b) (map_node008 f a b))
def node021 {G : Type*} [Monoid G] (a b : G) : G := node020 a b*node005 a b
theorem map_node021 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node021 a b)=node021 (f a) (f b) := by
  change f (node020 a b*node005 a b)=node020 (f a) (f b)*node005 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node020 f a b) (map_node005 f a b))
def node022 {G : Type*} [Monoid G] (a b : G) : G := node021 a b*node012 a b
theorem map_node022 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node022 a b)=node022 (f a) (f b) := by
  change f (node021 a b*node012 a b)=node021 (f a) (f b)*node012 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node021 f a b) (map_node012 f a b))
def node023 {G : Type*} [Monoid G] (a b : G) : G := node022 a b*node000 a b
theorem map_node023 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node023 a b)=node023 (f a) (f b) := by
  change f (node022 a b*node000 a b)=node022 (f a) (f b)*node000 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node022 f a b) (map_node000 f a b))
def node024 {G : Type*} [Monoid G] (a b : G) : G := node023 a b*node008 a b
theorem map_node024 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node024 a b)=node024 (f a) (f b) := by
  change f (node023 a b*node008 a b)=node023 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node023 f a b) (map_node008 f a b))
def node025 {G : Type*} [Monoid G] (a b : G) : G := node024 a b*node008 a b
theorem map_node025 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node025 a b)=node025 (f a) (f b) := by
  change f (node024 a b*node008 a b)=node024 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node024 f a b) (map_node008 f a b))
def node026 {G : Type*} [Monoid G] (a b : G) : G := node025 a b*node008 a b
theorem map_node026 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node026 a b)=node026 (f a) (f b) := by
  change f (node025 a b*node008 a b)=node025 (f a) (f b)*node008 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node025 f a b) (map_node008 f a b))
def node027 {G : Type*} [Monoid G] (a b : G) : G := node026 a b*node014 a b
theorem map_node027 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node027 a b)=node027 (f a) (f b) := by
  change f (node026 a b*node014 a b)=node026 (f a) (f b)*node014 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node026 f a b) (map_node014 f a b))
def node028 {G : Type*} [Monoid G] (a b : G) : G := node027 a b*node014 a b
theorem map_node028 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node028 a b)=node028 (f a) (f b) := by
  change f (node027 a b*node014 a b)=node027 (f a) (f b)*node014 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node027 f a b) (map_node014 f a b))
def node029 {G : Type*} [Monoid G] (a b : G) : G := node028 a b*node014 a b
theorem map_node029 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node029 a b)=node029 (f a) (f b) := by
  change f (node028 a b*node014 a b)=node028 (f a) (f b)*node014 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node028 f a b) (map_node014 f a b))
def node030 {G : Type*} [Monoid G] (a b : G) : G := node029 a b*node010 a b
theorem map_node030 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node030 a b)=node030 (f a) (f b) := by
  change f (node029 a b*node010 a b)=node029 (f a) (f b)*node010 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node029 f a b) (map_node010 f a b))
def node031 {G : Type*} [Monoid G] (a b : G) : G := node030 a b*node000 a b
theorem map_node031 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node031 a b)=node031 (f a) (f b) := by
  change f (node030 a b*node000 a b)=node030 (f a) (f b)*node000 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node030 f a b) (map_node000 f a b))
def node032 {G : Type*} [Monoid G] (a b : G) : G := node031 a b*node014 a b
theorem map_node032 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node032 a b)=node032 (f a) (f b) := by
  change f (node031 a b*node014 a b)=node031 (f a) (f b)*node014 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node031 f a b) (map_node014 f a b))
def node033 {G : Type*} [Monoid G] (a b : G) : G := node032 a b*node005 a b
theorem map_node033 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node033 a b)=node033 (f a) (f b) := by
  change f (node032 a b*node005 a b)=node032 (f a) (f b)*node005 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node032 f a b) (map_node005 f a b))
def node034 {G : Type*} [Monoid G] (a b : G) : G := node033 a b*node010 a b
theorem map_node034 {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (a b : G) : f (node034 a b)=node034 (f a) (f b) := by
  change f (node033 a b*node010 a b)=node033 (f a) (f b)*node010 (f a) (f b)
  exact (map_mul f _ _).trans (congrArg₂ (fun x y : K => x*y) (map_node033 f a b) (map_node010 f a b))
end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryWords
