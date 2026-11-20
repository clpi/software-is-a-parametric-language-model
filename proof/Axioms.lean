/-
  The dependency audit for the parametric rewritable
  language model core. Every theorem of the core is printed
  with the foundational principles it depends on; the family
  gate fails if any printed principle lies outside the
  allowed set of three.
-/

import Prlm

open Prlm

#print axioms feqrefl
#print axioms feqsymm
#print axioms feqtrans
#print axioms flerefl
#print axioms fletrans
#print axioms fleofeq
#print axioms fmuleq
#print axioms fmulone
#print axioms fonemul
#print axioms fmulinv
#print axioms flemul
#print axioms Sel.selnone
#print axioms Sel.selmem
#print axioms Sel.selmax
#print axioms Sel.selfirst
#print axioms Sel.sel_spec
#print axioms Sel.memsplit
#print axioms Sel.spec_unique
#print axioms appendinj
#print axioms completes_extends
#print axioms pairwise_flatmap
#print axioms completes_nodup
#print axioms decode_spec
#print axioms decode_determined
#print axioms cert_sound
#print axioms cert_blocked
#print axioms fmulassoc
#print axioms fmul_pos2
#print axioms multat_inv
#print axioms multat_pos
#print axioms overlay_roundtrip
#print axioms wscore_congr
#print axioms overlay_empty
#print axioms overlay_roundtrip_score
#print axioms multat_none
#print axioms overlay_cone
#print axioms ascore_agree
#print axioms ascore_reuse
#print axioms greedy_control
#print axioms blocked_control
