import LebesgueCover.TreeK
import LebK.Root4

/-!
# The vertex table for the four-body certificate
-/

open LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- The vertex table for `B₃, B₅, B₇`. -/
theorem vt4 : VertTableOK ns4 VQ nu4 := vertTable_ok (by decide)

end LebesgueCover.Cert
