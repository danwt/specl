; lemma
(set-info :status unsat)
(set-logic AUFLIRA)
(declare-fun Reach_22_n () Int)
(declare-fun Reach_24_n () Int)
(declare-fun Reach_7_n () Int)
(assert
 (let ((?x202079 (* Reach_24_n Reach_22_n)))
 (let ((?x202086 (* (- 1) ?x202079)))
 (let ((?x207080 (+ Reach_7_n ?x202086)))
 (<= ?x207080 0)))))
(assert
 (>= Reach_7_n 0))
(assert
 (let (($x33809 (>= Reach_22_n 0)))
 (not $x33809)))
(assert
 (>= Reach_24_n 1))
(assert
 (let (($x1912 (>= Reach_24_n 2)))
 (not $x1912)))
(assert
 (not false))
(check-sat)
