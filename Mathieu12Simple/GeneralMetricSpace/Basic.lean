import Mathieu12Simple.GPseudoMetricSpace.Basic
import Mathlib.Algebra.Order.Monoid.Defs

universe u v

variable {α:Type u} {β :Type v} [LinearOrderedAddCommMonoid β]


class GMetricSpace (α : Type u) (β : Type v) [LinearOrderedAddCommMonoid β] extends GPseudoMetricSpace α β where
  eq_of_dist_eq_zero : ∀ {x y : α}, gdist x y = 0 → x = y

/-- Two metric space structures with the same distance coincide. -/
@[ext]
theorem GMetricSpace.ext {α : Type*} {m m' : GMetricSpace α β} (h : m.toGDist = m'.toGDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption
