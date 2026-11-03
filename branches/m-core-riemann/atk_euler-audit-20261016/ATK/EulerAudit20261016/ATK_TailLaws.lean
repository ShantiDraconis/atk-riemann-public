import Mathlib

namespace ATK.Discovery

structure TailDecomposition (x : ℝ) where
  head : ℝ
  tail : ℝ
  reconstruct : x = head + tail

theorem reconstruct_difference {x y : ℝ}
    (dx : TailDecomposition x) (dy : TailDecomposition y) :
    y - x = (dy.head - dx.head) + (dy.tail - dx.tail) := by
  rw [dx.reconstruct, dy.reconstruct]
  ring

theorem strict_iff_tail_balance {x y : ℝ}
    (dx : TailDecomposition x) (dy : TailDecomposition y) :
    (x < y ↔ dx.head - dy.head < dy.tail - dx.tail) := by
  rw [dx.reconstruct, dy.reconstruct]
  constructor <;> intro h <;> linarith

theorem strict_of_equal_heads {x y : ℝ}
    (dx : TailDecomposition x) (dy : TailDecomposition y)
    (h : dx.head = dy.head) :
    (x < y ↔ dx.tail < dy.tail) := by
  rw [dx.reconstruct, dy.reconstruct, h]
  exact add_lt_add_iff_left dy.head

theorem zero_tail_of_exact_head {x : ℝ}
    (d : TailDecomposition x) (h : d.head = x) :
    d.tail = 0 := by
  have hr := d.reconstruct
  linarith

theorem p01_exact_counterexample : ¬ ((1 : ℕ) < 1) := by
  omega

theorem bounded_tail_strict {x y δ : ℝ}
    (dx : TailDecomposition x) (dy : TailDecomposition y)
    (hδ : 0 < δ)
    (hx0 : 0 ≤ dx.tail) (hxδ : dx.tail < δ)
    (hy0 : 0 ≤ dy.tail) (hyδ : dy.tail < δ)
    (hgap : δ ≤ dy.head - dx.head) :
    x < y := by
  rw [dx.reconstruct, dy.reconstruct]
  linarith

end ATK.Discovery