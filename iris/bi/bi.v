From iris.bi Require Export derived_laws derived_laws_later big_op.
From iris.bi Require Export updates internal_eq plainly embedding.
From iris.prelude Require Import options.

Module Import bi.
  (* The universe of the logic *)
  Universe L.
  Constraint L = interface.L.
  (* The universe of quantifiers in the logic *)
  Universe LQ.
  Constraint LQ = interface.LQ.
  Export bi.interface.bi.
  Export bi.derived_laws.bi.
  Export bi.derived_laws_later.bi.
End bi.
