// tests that LP detects multiple requires when using escaped identifier
require tests.OK.{|a b|}.{|escape file|};
require {|tests|}.OK.{|a b|}.{|escape file|};
