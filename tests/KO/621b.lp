// test that identifiers incompatible with Bindlib are rejected

symbol Typ : TYPE;
symbol eta : Typ → TYPE;

symbol id {|:00|} (Hb: eta {|:0|}) ≔ Hb;
