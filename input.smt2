(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(assert (not (= x (_ bv10 32))))
(check-sat)
(exit)
