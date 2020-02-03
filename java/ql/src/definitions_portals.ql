import java
import semmle.code.java.Portals

from Portal p
select p.getAnExitNode(), p.getAnEntryNode()
