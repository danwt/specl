; lemma
(set-info :status unsat)
(set-logic AUFLIRA)
(declare-fun Reach_13_n () Int)
(declare-fun Reach_12_n () Int)
(declare-fun Reach_22_n () Int)
(assert
 (let ((?x36674 (* (- 1) Reach_13_n)))
 (let ((?x6482 (+ Reach_12_n ?x36674)))
 (<= ?x6482 0))))
(assert
 (>= Reach_22_n 2))
(assert
 (<= Reach_22_n 2))
(assert
 (let ((?x39506 (mod Reach_12_n Reach_22_n)))
 (let ((?x39508 (div Reach_12_n Reach_22_n)))
 (let ((?x39525 (* Reach_22_n ?x39508)))
 (let ((?x39526 (+ ?x39525 ?x39506)))
 (let ((?x39455 (* (- 1) ?x39526)))
 (let ((?x39456 (+ Reach_12_n ?x39455)))
 (>= ?x39456 0))))))))
(assert
 (>= Reach_13_n 1))
(assert
 (let ((?x39506 (mod Reach_12_n Reach_22_n)))
 (>= ?x39506 0)))
(assert
 (let ((?x39508 (div Reach_12_n Reach_22_n)))
 (let ((?x39565 (* (- 1) ?x39508)))
 (let ((?x39566 (+ Reach_13_n ?x39565)))
 (<= ?x39566 0)))))
(assert
 (not false))
(check-sat)
