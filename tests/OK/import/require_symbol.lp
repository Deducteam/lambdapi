// The following is invalid because [symbol] is a keyword.
//require tests.OK.symbol

// Here is a workaround with an escaped identifier.
require tests.OK.{|symbol|};
