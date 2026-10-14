module

public import Mathlib
public import RequestProject.RodCircles

/-!
# Scaling a rod to its square (kernel-checked instances)

In these instances, going from the rod `p` to the rod `p²` multiplies the number of points on a
circle by `p`:

* `rod_121_square`, `rod_121_hex`: `121 = 11²` carries `11·12 = 132` points on both circles
  (the rod `11` carries `12`);
* `rod_361_hex`: `361 = 19²` carries `19·18 = 342` points on the hexagonal (flower) circle
  (the rod `19` carries `18`).

These are finite checks run by the Lean kernel, not a general theorem about all `p^k`.
-/

@[expose] public section

namespace RodCircles

theorem rod_121_square :
    (formPts (ZMod 121) 1 0 1).card = 132 := by
  decide +kernel

theorem rod_121_hex : (formPts (ZMod 121) 1 1 1).card = 132 := by
  decide +kernel

theorem rod_361_hex : (formPts (ZMod 361) 1 1 1).card = 342 := by
  decide +kernel

end RodCircles
