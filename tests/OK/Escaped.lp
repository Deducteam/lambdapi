// used in tests/dtrees.sh

// The following is accepted.
symbol {|symbol|} : TYPE;

// Escaped with dots (used to test module resolution)
symbol {|KIND.OF.BLUE|}: TYPE;

// Escaped with some rules
symbol {|let|} : TYPE;
rule {|let|} ↪ {|symbol|};
