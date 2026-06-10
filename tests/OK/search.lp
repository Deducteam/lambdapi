// Data type of booleans.
symbol bool : TYPE;
symbol nat : TYPE;
search name = B;;
search spine >= (nat → nat) , hyp >= bool;;
search hyp = (nat → bool);;
