
include "church.typ";
include "prod.typ";

let easy_inf n:Nat m:Nat =
  let A u m =
    let H = \c. pair (S (pi1 c)) (S (u (pi1 c))) in
    m H (pair 0 0) False in
  n A (\p.0) m
;

(*include "inf.typ";*)