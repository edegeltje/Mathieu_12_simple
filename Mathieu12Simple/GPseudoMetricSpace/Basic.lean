import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.Bornology.Basic
import Mathlib.Tactic

universe u v

variable {α:Type u} {β :Type v} [LinearOrderedAddCommMonoid β]
@[ext]
class GDist (α : Type u) (β :Type v) [LinearOrderedAddCommMonoid β] where
  gdist : α → α → β

open Set
open scoped BigOperators Topology

-- create all bounded sets?
@[reducible]
def Bornology.ofGDist (gdist : α → α → β) (gdist_comm : ∀ x y, gdist x y = gdist y x)
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
  gdist_self : ∀ x : α, gdist x x = 0
  gdist_comm : ∀ x y : α, gdist x y = gdist y x
  gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z
  toBornology : Bornology α := Bornology.ofGDist gdist gdist_comm gdist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : β, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, gdist x y ≤ C } := by intros; rfl

private theorem gdist_nonneg' {x y : α} (gdist : α → α → β)
    (gdist_self : ∀ x : α, gdist x x = 0) (gdist_comm : ∀ x y : α, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z) : 0 ≤ gdist x y := by
  have : 0 ≤ gdist x y + gdist x y :=
    calc 0 = gdist x x := (gdist_self _).symm
    _ ≤ gdist x y + gdist y x := gdist_triangle _ _ _
    _ = gdist x y + gdist x y:= by rw [gdist_comm]
  exact nonneg_add_self_iff.mp this

@[ext]
theorem GPseudoMetricSpace.ext {m m' : GPseudoMetricSpace α β}
    (h : m.toGDist = m'.toGDist) : m = m' := by
  cases' m with d _ _ _ B hB
  cases' m' with d' _ _ _ B' hB'
  obtain rfl : d = d' := h
  congr
  · ext : 2
    rw [← Filter.mem_sets, ← Filter.mem_sets, hB, hB']

variable [GPseudoMetricSpace α β]

@[simp]
theorem gdist_self (x : α) : GDist.gdist x x = (0:β) :=
  GPseudoMetricSpace.gdist_self x

theorem gdist_comm (x y : α) : GDist.gdist x y = (GDist.gdist y x:β) :=
  GPseudoMetricSpace.gdist_comm x y

theorem gdist_triangle (x y z : α) : GDist.gdist x z ≤ (GDist.gdist x y + GDist.gdist y z:β) :=
  GPseudoMetricSpace.gdist_triangle x y z


theorem gdist_triangle_left (x y z : α) : GDist.gdist x y ≤ (GDist.gdist z x + GDist.gdist z y:β) := by
  rw [gdist_comm z]; apply gdist_triangle


theorem gdist_triangle_right (x y z : α) : GDist.gdist x y ≤ (GDist.gdist x z + GDist.gdist y z:β) := by
  rw [gdist_comm y]; apply gdist_triangle


theorem gdist_triangle4 (x y z w : α) : GDist.gdist x w ≤ (GDist.gdist x y + GDist.gdist y z + GDist.gdist z w:β) :=
  calc
    GDist.gdist x w ≤ GDist.gdist x z + GDist.gdist z w := gdist_triangle x z w
    _ ≤ (GDist.gdist x y + GDist.gdist y z + GDist.gdist z w:β) := add_le_add_right (gdist_triangle x y z) _


theorem gdist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    GDist.gdist x₂ y₂ ≤ (GDist.gdist x₁ y₁ + (GDist.gdist x₁ x₂ + GDist.gdist y₁ y₂):β ) := by
  rw [add_left_comm, gdist_comm x₁, ← add_assoc]
  apply gdist_triangle4


theorem gdist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    GDist.gdist x₁ y₁ ≤ (GDist.gdist x₁ x₂ + GDist.gdist y₁ y₂ + GDist.gdist x₂ y₂:β ) := by
  rw [add_right_comm, gdist_comm y₁]
  apply gdist_triangle4


/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem gdist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    GDist.gdist (f m) (f n) ≤ (∑ i in Finset.Ico m n, GDist.gdist (f i) (f (i + 1)):β ) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, gdist_self]
  | succ n hle ihn =>
    calc
      GDist.gdist (f m) (f (n + 1)) ≤ GDist.gdist (f m) (f n) + GDist.gdist (f n) (f (n + 1)) := gdist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
      { rw [Nat.Ico_succ_right_eq_insert_Ico hle, Finset.sum_insert, add_comm]; simp }


/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem gdist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    GDist.gdist (f 0) (f n) ≤ (∑ i in Finset.range n, GDist.gdist (f i) (f (i + 1)) :β ) :=
  Nat.Ico_zero_eq_range ▸ gdist_le_Ico_sum_dist f (Nat.zero_le n)


/-- A version of `gdist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem gdist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → β}
    (hd : ∀ {k}, m ≤ k → k < n → GDist.gdist (f k) (f (k + 1)) ≤ d k) :
    GDist.gdist (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (gdist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2


/-- A version of `gdist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem gdist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → β}
    (hd : ∀ {k}, k < n → GDist.gdist (f k) (f (k + 1)) ≤ d k) :
    GDist.gdist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ gdist_le_Ico_sum_of_dist_le (zero_le n) fun _ => hd


theorem swap_gdist : Function.swap GDist.gdist = (GDist.gdist:α → α → β) := by funext x y; exact gdist_comm _ _


theorem gdist_nonneg {x y : α} : 0 ≤ (GDist.gdist x y:β) :=
  gdist_nonneg' GDist.gdist gdist_self gdist_comm gdist_triangle
