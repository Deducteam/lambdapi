symbol U: TYPE
symbol T: U ⇒ TYPE
symbol bool: U
symbol Bool: TYPE
rule T bool → Bool

hint hint_unif (T &x) Bool → hint_unif &x bool
