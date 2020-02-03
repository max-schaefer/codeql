/**
 * @name Jump-to-definition links
 * @description Generates use-definition pairs that provide the data
 *              for jump-to-definition in the code viewer.
 * @kind definitions
 * @id js/jump-to-definition
 */

import javascript
import definitions

from Locatable ref, ASTNode decl, string kind
where
  variableDefLookup(ref, decl, kind)
  or
  // prefer definitions over declarations
  not variableDefLookup(ref, _, _) and variableDeclLookup(ref, decl, kind)
  or
  importLookup(ref, decl, kind)
  or
  propertyLookup(ref, decl, kind)
  or
  typeLookup(ref, decl, kind)
  or
  typedInvokeLookup(ref, decl, kind)
  or
  jsdocTypeLookup(ref, decl, kind)
select ref, decl, kind
