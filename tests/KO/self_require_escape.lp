// test that require detects a circular dependency
// when using escaped identifiers
require tests.KO.{|self_require_escape|};
