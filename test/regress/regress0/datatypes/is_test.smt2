(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-datatypes () ((Unit (u))))
(declare-fun x () Unit)
(assert (not (is-u x)))
(check-sat)
