/**
 * @title Obfuscated string literal
 * @description String literals that use escape sequences to encode printable characters
 *              may be deliberately obfuscated, and might indicate malicious code.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id js/obfuscated-string-literal
 * @tags security
 *       external/cwe/cwe-506
 */

import javascript

from StringLiteral s
where
  // the string literal consists entirely of hex/unicode escape sequences
  s.getRawValue().regexpMatch(".(\\\\x[0-9a-fA-F]{2}|\\\\u[{]?[0-9a-fA-F]+[}]?)+.") and
  // but it is actually a printable ASCII string
  s.getValue().regexpMatch("[\\x20-\\x7e]+") and
  // exclude very short strings
  s.getValue().length() >= 5
select s, "This string literal looks deliberately obfuscated (its value is '" + s.getValue() + "')."
