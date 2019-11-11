require open tests.OK.private_export

symbol myz : A
symbol myg : A ⇒ A
rule myg _ → g myz

compute myg myz
type z
