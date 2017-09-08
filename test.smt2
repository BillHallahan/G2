(declare-datatypes () ((ApplyType_n__0 ApplyCon_n__0 ) ))
(declare-const fs?_n__0 ApplyType_n__0)
(declare-const fs?_n__1 Int)
(assert (= fs?_n__0 ApplyCon_n__0))
(assert (= fs?_n__0 ApplyCon_n__0))
(assert (= fs?_n__0 ApplyCon_n__0))

(check-sat)
(get-model)