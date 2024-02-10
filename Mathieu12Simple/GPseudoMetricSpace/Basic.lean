import Mathlib.Init.Order.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.Bornology.Basic

universe u v

variable {a:Type u} {β :Type v} [LinearOrderedAddCommMonoid β]
@[ext]
class GDist (α : Type u) (β :Type v) [LinearOrderedAddCommMonoid β] where
  gdist : α → α → β

open Set
-- create all bounded sets?
def Bornology.ofDist (gdist : α → α → β) (gdist_comm : ∀ x y, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z, gdist x z ≤ gdist x y + gdist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → gdist x y ≤ C }
    ⟨0,fun x hx y => hx.elim⟩
    (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, gdist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (gdist_triangle a x b).trans ?_⟩
        simpa only [gdist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (gdist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (gdist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨gdist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩



class GPseudoMetricSpace (α : Type u) (β:Type v) [LinearOrderedAddCommMonoid β] extends GDist α β where
  dist_self : ∀ x : α, gdist x x = 0
  dist_comm : ∀ x y : α, gdist x y = gdist y x
  dist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z
  toBornology : Bornology α := Bornology.ofDist gdist dist_comm dist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : β, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, gdist x y ≤ C } := by intros; rfl
