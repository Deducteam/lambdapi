symbol o : TYPE
symbol not : o → o
set prefix 5 "~" ≔ not
type λp x,~(p x)
type λp x,~ p x
//assert λp x,~(p x) ≡ λp x,~ p x
