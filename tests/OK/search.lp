// Data type of booleans.
symbol bool : TYPE;
symbol nat : TYPE;
search name = B in "est";
search name = B | name = C;
search spine >= (nat → nat) | hyp >= bool;
search hyp = (nat → bool);
