// The following is forbidden as [KIND] is reserved.
//symbol KIND : TYPE;

// The following is accepted.
symbol {|KIND|} : TYPE;

// Escaped with dots (used to test module resolution)
symbol {|KIND.OF.BLUE|}: TYPE;

// Escaped with some rules
symbol {|_set|} : TYPE;
rule {|_set|} ↪ {|KIND|};
